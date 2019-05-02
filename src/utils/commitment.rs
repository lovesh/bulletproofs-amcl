use crate::utils::group_elem::{GroupElement, GroupElementVector};
use crate::utils::field_elem::{FieldElement, FieldElementVector};
use crate::errors::ValueError;

// Commit to field element `elem` with randomness `r` given groups elements `g` and `h`, i.e. compute g^elem.h^r
pub fn commit_to_field_element(g: &GroupElement, h: &GroupElement, elem: &FieldElement,
                               r: &FieldElement) -> GroupElement {
    let elem_g = g * elem;
    let r_h = h * r;
    elem_g + r_h
}

/// Commit to field element vectors `a` and `b` with random field element `c`
/// Given group element vectors `g` and `h` and group element `u`, compute
/// (a1*g1 + a2*g2 + a3*g3) + (b1*h1 + b2*h2 + b3*h3) + c*u
pub fn commit_to_field_element_vectors(g: &GroupElementVector, h: &GroupElementVector, u: &GroupElement,
                                       a: &FieldElementVector, b: &FieldElementVector, c: &FieldElement) -> Result<GroupElement, ValueError> {
    let a_g = g.inner_product(a)?;
    let b_h = h.inner_product(b)?;
    let c_u = u * c;
    Ok(a_g + b_h + c_u)
}