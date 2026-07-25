use super::*;

#[test]
fn add_i64_basic() {
    assert_eq!(add_i64(2, 3), 5);
    assert_eq!(add_i64(-1, 1), 0);
}

#[test]
fn sub_i64_basic() {
    assert_eq!(sub_i64(5, 2), 3);
    assert_eq!(sub_i64(0, 7), -7);
}

#[test]
fn mul_i64_basic() {
    assert_eq!(mul_i64(3, 4), 12);
    assert_eq!(mul_i64(-2, 3), -6);
}

#[test]
fn div_i64_basic() {
    assert_eq!(div_i64(10, 2), 5);
    assert_eq!(div_i64(-7, 2), -3); // truncated toward zero (matches sdiv)
}

#[test]
fn add_f64_round_trip() {
    let a: f64 = 1.5;
    let b: f64 = 2.25;
    let r = add_f64(a.to_bits() as i64, b.to_bits() as i64);
    assert_eq!(f64::from_bits(r as u64), 3.75);
}

#[test]
fn eq_i64_returns_bool_i64() {
    assert_eq!(eq_i64(3, 3), 1);
    assert_eq!(eq_i64(3, 4), 0);
}

#[test]
fn lt_i64_basic() {
    assert_eq!(lt_i64(1, 2), 1);
    assert_eq!(lt_i64(2, 1), 0);
    assert_eq!(lt_i64(1, 1), 0);
}

#[test]
fn not_flips_bool() {
    assert_eq!(not(0), 1);
    assert_eq!(not(1), 0);
}

#[test]
fn eq_bool_basic() {
    assert_eq!(eq_bool(1, 1), 1);
    assert_eq!(eq_bool(0, 1), 0);
}

#[test]
fn neq_f64_basic() {
    let a: f64 = 1.5;
    let b: f64 = 2.5;
    assert_eq!(neq_f64(a.to_bits() as i64, b.to_bits() as i64), 1);
    assert_eq!(neq_f64(a.to_bits() as i64, a.to_bits() as i64), 0);
}
