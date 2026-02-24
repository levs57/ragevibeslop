use crate::error::{Error, Result};
use ark_ff::Field;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LaurentMonomial {
    // (alpha, beta, gamma, delta, rho, tau)
    exponents: [i64; 6],
}

impl LaurentMonomial {
    pub fn one() -> Self {
        Self { exponents: [0; 6] }
    }

    pub fn from_powers(powers: &[(&str, i64)]) -> Self {
        let mut m = Self::one();
        for (sym, exp) in powers {
            let idx = symbol_index(sym)
                .unwrap_or_else(|| panic!("unsupported Laurent symbol: {sym}"));
            m.exponents[idx] += *exp;
        }
        m
    }

    pub fn from_symbol<S: Into<String>>(symbol: S) -> Self {
        let s = symbol.into();
        let mut m = Self::one();
        if let Some(base) = s.strip_suffix("_INV") {
            let idx = symbol_index(base)
                .unwrap_or_else(|| panic!("unsupported Laurent symbol: {s}"));
            m.exponents[idx] = -1;
            return m;
        }
        let idx = symbol_index(&s).unwrap_or_else(|| panic!("unsupported Laurent symbol: {s}"));
        m.exponents[idx] = 1;
        m
    }

    pub fn mul(&self, other: &Self) -> Self {
        let mut out = [0i64; 6];
        for (i, slot) in out.iter_mut().enumerate() {
            *slot = self.exponents[i] + other.exponents[i];
        }
        Self { exponents: out }
    }
}

fn symbol_index(sym: &str) -> Option<usize> {
    match sym {
        "ALPHA" | "alpha" => Some(0),
        "BETA" | "beta" => Some(1),
        "GAMMA" | "gamma" => Some(2),
        "DELTA" | "delta" => Some(3),
        "RHO" | "rho" => Some(4),
        "TAU" | "tau" => Some(5),
        _ => None,
    }
}

impl Ord for LaurentMonomial {
    fn cmp(&self, other: &Self) -> Ordering {
        self.exponents.cmp(&other.exponents)
    }
}

impl PartialOrd for LaurentMonomial {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LaurentPolynomial<F: Field> {
    terms: BTreeMap<LaurentMonomial, F>,
}

impl<F: Field> LaurentPolynomial<F> {
    pub fn zero() -> Self {
        Self {
            terms: BTreeMap::new(),
        }
    }

    pub fn monomial(coeff: F, mono: LaurentMonomial) -> Self {
        if coeff.is_zero() {
            return Self::zero();
        }
        let mut terms = BTreeMap::new();
        terms.insert(mono, coeff);
        Self { terms }
    }

    pub fn add_term(&mut self, coeff: F, mono: LaurentMonomial) {
        if coeff.is_zero() {
            return;
        }
        let cur = self.terms.get(&mono).copied().unwrap_or_else(F::zero);
        let next = cur + coeff;
        if next.is_zero() {
            self.terms.remove(&mono);
        } else {
            self.terms.insert(mono, next);
        }
    }

    pub fn coeff_of(&self, mono: &LaurentMonomial) -> F {
        self.terms.get(mono).copied().unwrap_or_else(F::zero)
    }

    pub fn monomials(&self) -> impl Iterator<Item = &LaurentMonomial> {
        self.terms.keys()
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }
}

impl<F: Field> std::ops::Add for LaurentPolynomial<F> {
    type Output = Self;
    fn add(mut self, rhs: Self) -> Self::Output {
        for (m, c) in rhs.terms {
            self.add_term(c, m);
        }
        self
    }
}

impl<F: Field> std::ops::Sub for LaurentPolynomial<F> {
    type Output = Self;
    fn sub(mut self, rhs: Self) -> Self::Output {
        for (m, c) in rhs.terms {
            self.add_term(-c, m);
        }
        self
    }
}

impl<F: Field> std::ops::Mul for LaurentPolynomial<F> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        if self.is_zero() || rhs.is_zero() {
            return Self::zero();
        }
        let mut out = Self::zero();
        for (m1, c1) in self.terms {
            for (m2, c2) in &rhs.terms {
                out.add_term(c1 * *c2, m1.mul(m2));
            }
        }
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairingProduct<F: Field> {
    pub g1_index: usize,
    pub g2_index: usize,
    pub expression: LaurentPolynomial<F>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConstructibleKind {
    Pairing { g1_index: usize, g2_index: usize },
    GtElement { gt_index: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructibleElement<F: Field> {
    pub kind: ConstructibleKind,
    pub expression: LaurentPolynomial<F>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairingTerm<F: Field> {
    pub g1_index: usize,
    pub g2_index: usize,
    pub coeff: F,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructibleTerm<F: Field> {
    pub kind: ConstructibleKind,
    pub coeff: F,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AttackSolution<F: Field> {
    pub coefficients: Vec<F>,
    pub pairing_terms: Vec<PairingTerm<F>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConstructibleSolution<F: Field> {
    pub coefficients: Vec<F>,
    pub terms: Vec<ConstructibleTerm<F>>,
}

pub fn build_pairing_products<F: Field>(
    g1_elements: &[LaurentPolynomial<F>],
    g2_elements: &[LaurentPolynomial<F>],
) -> Vec<PairingProduct<F>> {
    let mut products = Vec::with_capacity(g1_elements.len() * g2_elements.len());
    for (i, g1) in g1_elements.iter().enumerate() {
        for (j, g2) in g2_elements.iter().enumerate() {
            products.push(PairingProduct {
                g1_index: i,
                g2_index: j,
                expression: g1.clone() * g2.clone(),
            });
        }
    }
    products
}

pub fn build_constructible_elements<F: Field>(
    g1_elements: &[LaurentPolynomial<F>],
    g2_elements: &[LaurentPolynomial<F>],
    gt_elements: &[LaurentPolynomial<F>],
) -> Vec<ConstructibleElement<F>> {
    let mut out = Vec::with_capacity(g1_elements.len() * g2_elements.len() + gt_elements.len());
    for (i, g1) in g1_elements.iter().enumerate() {
        for (j, g2) in g2_elements.iter().enumerate() {
            out.push(ConstructibleElement {
                kind: ConstructibleKind::Pairing {
                    g1_index: i,
                    g2_index: j,
                },
                expression: g1.clone() * g2.clone(),
            });
        }
    }
    for (i, gt) in gt_elements.iter().enumerate() {
        out.push(ConstructibleElement {
            kind: ConstructibleKind::GtElement { gt_index: i },
            expression: gt.clone(),
        });
    }
    out
}

pub fn solve_target_decomposition<F: Field>(
    products: &[PairingProduct<F>],
    target: &LaurentPolynomial<F>,
) -> Result<AttackSolution<F>> {
    let expressions: Vec<LaurentPolynomial<F>> =
        products.iter().map(|p| p.expression.clone()).collect();
    let x = solve_expression_system(&expressions, target)?;

    let mut pairing_terms = Vec::new();
    for (idx, coeff) in x.iter().enumerate() {
        if coeff.is_zero() {
            continue;
        }
        pairing_terms.push(PairingTerm {
            g1_index: products[idx].g1_index,
            g2_index: products[idx].g2_index,
            coeff: *coeff,
        });
    }

    Ok(AttackSolution {
        coefficients: x,
        pairing_terms,
    })
}

pub fn solve_target_from_constructible<F: Field>(
    elements: &[ConstructibleElement<F>],
    target: &LaurentPolynomial<F>,
) -> Result<ConstructibleSolution<F>> {
    let expressions: Vec<LaurentPolynomial<F>> =
        elements.iter().map(|e| e.expression.clone()).collect();
    let x = solve_expression_system(&expressions, target)?;

    let mut terms = Vec::new();
    for (idx, coeff) in x.iter().enumerate() {
        if coeff.is_zero() {
            continue;
        }
        terms.push(ConstructibleTerm {
            kind: elements[idx].kind.clone(),
            coeff: *coeff,
        });
    }

    Ok(ConstructibleSolution {
        coefficients: x,
        terms,
    })
}

fn solve_expression_system<F: Field>(
    expressions: &[LaurentPolynomial<F>],
    target: &LaurentPolynomial<F>,
) -> Result<Vec<F>> {
    let mut monomials = BTreeSet::new();
    for expr in expressions {
        for m in expr.monomials() {
            monomials.insert(m.clone());
        }
    }
    for m in target.monomials() {
        monomials.insert(m.clone());
    }

    let row_basis: Vec<LaurentMonomial> = monomials.into_iter().collect();
    let rows = row_basis.len();
    let cols = expressions.len();

    if cols == 0 {
        if target.is_zero() {
            return Ok(Vec::new());
        }
        return Err(Error::NoSymbolicProducts);
    }

    let mut aug = vec![vec![F::zero(); cols + 1]; rows];
    for (r, mono) in row_basis.iter().enumerate() {
        for (c, expr) in expressions.iter().enumerate() {
            aug[r][c] = expr.coeff_of(mono);
        }
        aug[r][cols] = target.coeff_of(mono);
    }

    let pivot_cols = rref(&mut aug, cols);

    for row in &aug {
        let lhs_all_zero = row[..cols].iter().all(|v| v.is_zero());
        if lhs_all_zero && !row[cols].is_zero() {
            return Err(Error::SymbolicSystemInconsistent);
        }
    }

    let mut x = vec![F::zero(); cols];
    for (pivot_row, pivot_col) in pivot_cols.iter().enumerate() {
        x[*pivot_col] = aug[pivot_row][cols];
    }

    if !verify_solution(expressions, &x, target, &row_basis) {
        return Err(Error::SymbolicSystemInconsistent);
    }

    Ok(x)
}

fn verify_solution<F: Field>(
    expressions: &[LaurentPolynomial<F>],
    coeffs: &[F],
    target: &LaurentPolynomial<F>,
    row_basis: &[LaurentMonomial],
) -> bool {
    for mono in row_basis {
        let mut lhs = F::zero();
        for (idx, expr) in expressions.iter().enumerate() {
            lhs += coeffs[idx] * expr.coeff_of(mono);
        }
        if lhs != target.coeff_of(mono) {
            return false;
        }
    }
    true
}

fn rref<F: Field>(aug: &mut [Vec<F>], num_cols: usize) -> Vec<usize> {
    let rows = aug.len();
    let mut r = 0usize;
    let mut pivot_cols = Vec::new();

    for c in 0..num_cols {
        if r >= rows {
            break;
        }

        let mut pivot = r;
        while pivot < rows && aug[pivot][c].is_zero() {
            pivot += 1;
        }
        if pivot == rows {
            continue;
        }

        if pivot != r {
            aug.swap(pivot, r);
        }

        let pivot_val = aug[r][c];
        for j in c..=num_cols {
            aug[r][j] /= pivot_val;
        }
        let pivot_row = aug[r].clone();

        for i in 0..rows {
            if i == r {
                continue;
            }
            let factor = aug[i][c];
            if factor.is_zero() {
                continue;
            }
            for j in c..=num_cols {
                aug[i][j] -= factor * pivot_row[j];
            }
        }

        pivot_cols.push(c);
        r += 1;
    }

    pivot_cols
}
