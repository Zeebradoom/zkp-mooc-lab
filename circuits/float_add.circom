pragma circom 2.0.0;

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////// Templates from the circomlib ////////////////////////////////
////////////////// Copy-pasted here for easy reference //////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `a` AND `b`
 */
template AND() {
    signal input a;
    signal input b;
    signal output out;

    out <== a*b;
}

/*
 * Outputs `a` OR `b`
 */
template OR() {
    signal input a;
    signal input b;
    signal output out;

    out <== a + b - a*b;
}

/*
 * `out` = `cond` ? `L` : `R`
 */
template IfThenElse() {
    signal input cond;
    signal input L;
    signal input R;
    signal output out;

    out <== cond * (L - R) + R;
}

/*
 * (`outL`, `outR`) = `sel` ? (`R`, `L`) : (`L`, `R`)
 */
template Switcher() {
    signal input sel;
    signal input L;
    signal input R;
    signal output outL;
    signal output outR;

    signal aux;

    aux <== (R-L)*sel;
    outL <==  aux + L;
    outR <== -aux + R;
}

/*
 * Decomposes `in` into `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 * Enforces that `in` is at most `b` bits long.
 */
template Num2Bits(b) {
    signal input in;
    signal output bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }
    sum_of_bits === in;
}

/*
 * Reconstructs `out` from `b` bits, given by `bits`.
 * Least significant bit in `bits[0]`.
 */
template Bits2Num(b) {
    signal input bits[b];
    signal output out;
    var lc = 0;

    for (var i = 0; i < b; i++) {
        lc += (bits[i] * (1 << i));
    }
    out <== lc;
}

/*
 * Checks if `in` is zero and returns the output in `out`.
 */
template IsZero() {
    signal input in;
    signal output out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}

/*
 * Checks if `in[0]` == `in[1]` and returns the output in `out`.
 */
template IsEqual() {
    signal input in[2];
    signal output out;

    component isz = IsZero();

    in[1] - in[0] ==> isz.in;

    isz.out ==> out;
}

/*
 * Checks if `in[0]` < `in[1]` and returns the output in `out`.
 * Assumes `n` bit inputs. The behavior is not well-defined if any input is more than `n`-bits long.
 */
template LessThan(n) {
    assert(n <= 252);
    signal input in[2];
    signal output out;

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.bits[n];
}

/////////////////////////////////////////////////////////////////////////////////////
///////////////////////// Templates for this lab ////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

/*
 * Outputs `out` = 1 if `in` is at most `b` bits long, and 0 otherwise.
 */
template CheckBitLength(b) {
    // signal input in;
    signal output out;

    // component zeroCheck = IsZero();
    // zeroCheck.in <-- in >> b;
    // out <== zeroCheck.out;

    signal input in;
    signal output bits[b];

    for (var i = 0; i < b; i++) {
        bits[i] <-- (in >> i) & 1;
        bits[i] * (1 - bits[i]) === 0;
    }
    var sum_of_bits = 0;
    for (var i = 0; i < b; i++) {
        sum_of_bits += (2 ** i) * bits[i];
    }

    component checkEqual = IsEqual();
    checkEqual.in <== [sum_of_bits, in];
    out <== checkEqual.out;

    
}

/*
 * Enforces the well-formedness of an exponent-mantissa pair (e, m), which is defined as follows:
 * if `e` is zero, then `m` must be zero
 * else, `e` must be at most `k` bits long, and `m` must be in the range [2^p, 2^p+1)
 */
template CheckWellFormedness(k, p) {
    signal input e;
    signal input m;

    // check if `e` is zero
    component is_e_zero = IsZero();
    is_e_zero.in <== e;

    // Case I: `e` is zero
    //// `m` must be zero
    component is_m_zero = IsZero();
    is_m_zero.in <== m;

    // Case II: `e` is nonzero
    //// `e` is `k` bits
    component check_e_bits = CheckBitLength(k);
    check_e_bits.in <== e;
    //// `m` is `p`+1 bits with the MSB equal to 1
    //// equivalent to check `m` - 2^`p` is in `p` bits
    component check_m_bits = CheckBitLength(p);
    check_m_bits.in <== m - (1 << p);

    // choose the right checks based on `is_e_zero`
    component if_else = IfThenElse();
    if_else.cond <== is_e_zero.out;
    if_else.L <== is_m_zero.out;
    //// check_m_bits.out * check_e_bits.out is equivalent to check_m_bits.out AND check_e_bits.out
    if_else.R <== check_m_bits.out * check_e_bits.out;

    // assert that those checks passed
    if_else.out === 1;
}

/*
 * Right-shifts `b`-bit long `x` by `shift` bits to output `y`, where `shift` is a public circuit parameter.
 */
template RightShift(b, shift) {
    signal input x;
    signal output y;

    signal rem <-- x % (1 << shift);
    component num2bits = Num2Bits(b);
    num2bits.in <== x;

    y <-- (x - rem) / (1 << shift);
    x === y * (1 << shift) + rem;


}

/*
 * Rounds the input floating-point number and checks to ensure that rounding does not make the mantissa unnormalized.
 * Rounding is necessary to prevent the bitlength of the mantissa from growing with each successive operation.
 * The input is a normalized floating-point number (e, m) with precision `P`, where `e` is a `k`-bit exponent and `m` is a `P`+1-bit mantissa.
 * The output is a normalized floating-point number (e_out, m_out) representing the same value with a lower precision `p`.
 */
template RoundAndCheck(k, p, P) {
    signal input e;
    signal input m;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // check if no overflow occurs
    component if_no_overflow = LessThan(P+1);
    if_no_overflow.in[0] <== m;
    if_no_overflow.in[1] <== (1 << (P+1)) - (1 << (P-p-1));
    signal no_overflow <== if_no_overflow.out;

    var round_amt = P-p;
    // Case I: no overflow
    // compute (m + 2^{round_amt-1}) >> round_amt
    var m_prime = m + (1 << (round_amt-1));
    //// Although m_prime is P+1 bits long in no overflow case, it can be P+2 bits long
    //// in the overflow case and the constraints should not fail in either case
    component right_shift = RightShift(P+2, round_amt);
    right_shift.x <== m_prime;
    var m_out_1 = right_shift.y;
    var e_out_1 = e;

    // Case II: overflow
    var e_out_2 = e + 1;
    var m_out_2 = (1 << p);

    // select right output based on no_overflow
    component if_else[2];
    for (var i = 0; i < 2; i++) {
        if_else[i] = IfThenElse();
        if_else[i].cond <== no_overflow;
    }
    if_else[0].L <== e_out_1;
    if_else[0].R <== e_out_2;
    if_else[1].L <== m_out_1;
    if_else[1].R <== m_out_2;
    e_out <== if_else[0].out;
    m_out <== if_else[1].out;
}

/*
 * Left-shifts `x` by `shift` bits to output `y`.
 * Enforces 0 <= `shift` < `shift_bound`.
 * If `skip_checks` = 1, then we don't care about the output and the `shift_bound` constraint is not enforced.
 */
template LeftShift(shift_bound) {
    signal input x;
    signal input shift;
    signal input skip_checks;
    signal output y;

    component checkZero = LessThan(252);
    checkZero.in[0] <== -1;
    checkZero.in[1] <== shift;
    checkZero.out === 1;
    
    // if its 1 it swaps, 0 it doesnt
    component switchh = Switcher();
    switchh.sel <== skip_checks;
    switchh.L <== shift;
    switchh.R <== 0;

    component shift_bound_check = LessThan(shift_bound);
    shift_bound_check.in[0] <== switchh.outL;
    shift_bound_check.in[1] <== shift_bound;
    shift_bound_check.out === 1;

    //following code takes the exponent of 2^shift 
    var maxBits = 8;

    signal exp[maxBits];
    signal holdTempVal[maxBits];
    signal temp[maxBits];

    component num2Bits = Num2Bits(maxBits);
    num2Bits.in <== shift;

    signal temp2;

    exp[0] <== 2;
    holdTempVal[0] <== 1;
    for (var i = 0; i < maxBits; i++) {
        temp[i] <== num2Bits.bits[i] * exp[i] + (1 - num2Bits.bits[i]); //if num2Bits.bits[i] is 1, then temp[i] = exp[i], else temp[i] = 1
        if (i < maxBits - 1) {
            holdTempVal[i + 1] <== holdTempVal[i] * temp[i];
            exp[i + 1] <== exp[i] * exp[i];
        } else {
            temp2 <== holdTempVal[i] * temp[i];
        }
    }

    //multiplies this 2^shift by y, left shifting it while ensuring soundness
    y <== x * temp2;

}

/*
 * Find the Most-Significant Non-Zero Bit (MSNZB) of `in`, where `in` is assumed to be non-zero value of `b` bits.
 * Outputs the MSNZB as a one-hot vector `one_hot` of `b` bits, where `one_hot`[i] = 1 if MSNZB(`in`) = i and 0 otherwise.
 * The MSNZB is output as a one-hot vector to reduce the number of constraints in the subsequent `Normalize` template.
 * Enforces that `in` is non-zero as MSNZB(0) is undefined.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template MSNZB(b) {
    signal input in;
    signal input skip_checks;
    signal output one_hot[b];

    //check if valid skip_checks or in value
    component lessCheck = LessThan(b);
    lessCheck.in[0] <== 0;
    lessCheck.in[1] <== in + skip_checks;
    lessCheck.out === 1;

    //convert all to bits
    component num2bits = Num2Bits(b);
    num2bits.in <== in;

    //use suffix product to create mask
    signal mask[b];
    mask[b-1] <== 1;
    for (var i = b-2; i >= 0; i--) {
        mask[i] <== mask[i+1] * (1 - num2bits.bits[i+1]);
    }

    for (var i = 0; i < b; i++) {
        one_hot[i] <== num2bits.bits[i] * mask[i];
    }

    //check suffix product if sound
    component checkSound = IfThenElse();
    checkSound.cond <== skip_checks;
    checkSound.L <== 0;
    checkSound.R <== mask[0] * (1-num2bits.bits[0]);

    checkSound.out === 0;

}

/*
 * Normalizes the input floating-point number.
 * The input is a floating-point number with a `k`-bit exponent `e` and a 
 `P`+1-bit *unnormalized* mantissa `m` with precision `p`, where `m` is assumed to be non-zero.
 * The output is a floating-point number representing the same value with exponent 
 `e_out` and a *normalized* mantissa `m_out` of `P`+1-bits and precision `P`.
 * Enforces that `m` is non-zero as a zero-value can not be normalized.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero 
 constraint is not enforced.
 */

template Normalize(k, p, P) {
    signal input e;
    signal input m;
    signal input skip_checks;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    //finds the most significant non-zero bit
    component msnzb_finder = MSNZB(P + 1);
    msnzb_finder.in <== m;
    msnzb_finder.skip_checks <== skip_checks;

    //finds the exponent difference
    signal one_hot_arr[P + 1] <== msnzb_finder.one_hot;
    var exponent_diff = 0;
    var idx;

    //sums the one_hot_arr
    for (idx = 0; idx <= P; idx++) {
        exponent_diff += idx * one_hot_arr[idx];
    }

    e_out <== e + exponent_diff - p;

    //shifts mantissa to the left
    signal shifting_value <== P - exponent_diff;
    component leftShiftComponent = LeftShift(252);
    leftShiftComponent.x <== m;
    leftShiftComponent.shift <== shifting_value;
    leftShiftComponent.skip_checks <== skip_checks;
    m_out <== leftShiftComponent.y;
}

/*
 * Adds two floating-point numbers.
 * The inputs are normalized floating-point numbers with `k`-bit exponents `e` and `p`+1-bit mantissas `m` with scale `p`.
 * Does not assume that the inputs are well-formed and makes appropriate checks for the same.
 * The output is a normalized floating-point number with exponent `e_out` and mantissa `m_out` of `p`+1-bits and scale `p`.
 * Enforces that inputs are well-formed.
 */

 template FloatAdd(k, p) {
    signal input e[2];
    signal input m[2];
    signal output e_out;
    signal output m_out;

    component check_wf[2];

    // Check well-formdness of the input numbers
    for (var i = 0; i < 2; i++) {
        check_wf[i] = CheckWellFormedness(k, p);
        check_wf[i].e <== e[i];
        check_wf[i].m <== m[i];
    }

    // ensure magnitude of e[0] <= magnitude of e[1]
    component cmp_magnitudes = LessThan(k + p + 1);
    for (var i = 0; i < 2; i++) {
        cmp_magnitudes.in[i] <== m[i] + e[i] * (1 << (p + 1));
    }

    // switch the inputs based on the magnitude comparison
    component switch_exponents = Switcher();
    component switch_mantissas = Switcher();
    
    switch_exponents.sel <== cmp_magnitudes.out;
    switch_exponents.L <== e[0];
    switch_exponents.R <== e[1];

    switch_mantissas.sel <== cmp_magnitudes.out;
    switch_mantissas.L <== m[0];
    switch_mantissas.R <== m[1];

    // compute the exponent difference
    var alpha_m = switch_mantissas.outL;
    var alpha_e = switch_exponents.outL;
    var beta_m = switch_mantissas.outR;
    var beta_e = switch_exponents.outR;

    signal exponent_diff <== alpha_e - beta_e;

    // check if the exponent difference is greater than p
    component diff_greater_check = LessThan(k);
    diff_greater_check.in[0] <== p + 1;
    diff_greater_check.in[1] <== exponent_diff;

    // if the exponent difference is greater than p, then the output is the
    // larger of the two inputs
    component alpha_e_is_zero = IsZero();
    alpha_e_is_zero.in <== alpha_e;

    component skip_condition = OR();
    skip_condition.a <== diff_greater_check.out;
    skip_condition.b <== alpha_e_is_zero.out;

    // Use If-Then-Else components to handle different cases
    //  If skip_condition.out is true, it selects the value 1. 
    //If false, it selects the value of alpha_m. 
    //This means that if the skip condition is met, the left-shift operation will be skipped, 
    //and the value of 1 will be used instead of the actual mantissa alpha_m.
    component if_else_alpha_m = IfThenElse();
    if_else_alpha_m.cond <== skip_condition.out;
    if_else_alpha_m.L <== 1;
    if_else_alpha_m.R <== alpha_m;

    //  If skip_condition.out is true, it selects the value 0. If false, it selects the value of exponent_diff. 
    component if_else_diff = IfThenElse();
    if_else_diff.cond <== skip_condition.out;
    if_else_diff.L <== 0;
    if_else_diff.R <== exponent_diff;

    //  If skip_condition.out is true, it selects the value 1. If false, it selects the value of beta_e.
    component if_else_beta_e = IfThenElse();
    if_else_beta_e.cond <== skip_condition.out;
    if_else_beta_e.L <== 1;
    if_else_beta_e.R <== beta_e;

    //shifts mantissa to the left
    component m_alpha_shift = LeftShift(p + 2);
    m_alpha_shift.x <== if_else_alpha_m.out;
    m_alpha_shift.shift <== if_else_diff.out;
    m_alpha_shift.skip_checks <== 0;

    // normalizes the result to fit within the required floating-point representation 
    component norm = Normalize(k, p, 2 * p + 1);
    norm.e <== if_else_beta_e.out;
    norm.m <== m_alpha_shift.y + beta_m;
    norm.skip_checks <== 0;

    // RoundAndCheck component that rounds 
    component round_chk = RoundAndCheck(k, p, 2 * p + 1);
    round_chk.e <== norm.e_out;
    round_chk.m <== norm.m_out;

    // selects the final exponent value based on the skip_condition.out. 
    //If the skip condition is true, the original exponent of the larger number (alpha_e) is selected; 
    //otherwise, the rounded exponent (round_chk.e_out) is used.
    component if_else_e_result = IfThenElse();
    if_else_e_result.cond <== skip_condition.out;
    if_else_e_result.L <== alpha_e;
    if_else_e_result.R <== round_chk.e_out;

    // If  skip condition is true, the original mantissa of the larger number (alpha_m) is selected; 
    //otherwise, the rounded mantissa (round_chk.m_out) is used.
    component if_else_m_result = IfThenElse();
    if_else_m_result.cond <== skip_condition.out;
    if_else_m_result.L <== alpha_m;
    if_else_m_result.R <== round_chk.m_out;

    e_out <== if_else_e_result.out;
    m_out <== if_else_m_result.out;
}


template FloatAdd(k, p) {
    signal input e[2];
    signal input m[2];
    signal output e_out;
    signal output m_out;

    // Check well formdness of the input numbers
    component checker[2];
    for (var i = 0; i < 2; i++) {
        checker[i] = CheckWellFormedness(k, p);
        checker[i].e <== e[i];
        checker[i].m <== m[i];
    }

    // Compare the magnitudes of the input numbers
    component Compare = LessThan(k + p + 1);
    for (var i = 0; i < 2; i++) {
        Compare.in[i] <== m[i] + e[i] * (1 << (p + 1));
    }

    // Switch the inputs based on the comparison result
    component eSwitch = Switcher();
    component mSwitch = Switcher();
    eSwitch.sel <== Compare.out;
    eSwitch.L <== e[0];
    eSwitch.R <== e[1];
    mSwitch.sel <== Compare.out;
    mSwitch.L <== m[0];
    mSwitch.R <== m[1];

    // Assign alpha and beta variables
    var alpha_m = mSwitch.outL;
    var alpha_e = eSwitch.outL;
    var beta_m = mSwitch.outR;
    var beta_e = eSwitch.outR;

    // Calculate the exponent difference and check conditions
    signal diff <== alpha_e - beta_e;
    component diff_check = LessThan(k);
    diff_check.in[0] <== p + 1;
    diff_check.in[1] <== diff;
    component alpha_e_check = IsZero();
    alpha_e_check.in <== alpha_e;
    component skip_condition = OR();
    skip_condition.a <== diff_check.out;
    skip_condition.b <== alpha_e_check.out;

    // Use If-Then-Else components to handle different cases
    component if_else_alpha_m = IfThenElse();
    if_else_alpha_m.cond <== skip_condition.out;
    if_else_alpha_m.L <== 1;
    if_else_alpha_m.R <== alpha_m;
    component if_else_diff = IfThenElse();
    if_else_diff.cond <== skip_condition.out;
    if_else_diff.L <== 0;
    if_else_diff.R <== diff;
    component if_else_beta_e = IfThenElse();
    if_else_beta_e.cond <== skip_condition.out;
    if_else_beta_e.L <== 1;
    if_else_beta_e.R <== beta_e;

    // Shift, normalize, and round the result
    component m_alpha_left_shift = LeftShift(p + 2);
    m_alpha_left_shift.x <== if_else_alpha_m.out;
    m_alpha_left_shift.shift <== if_else_diff.out;
    m_alpha_left_shift.skip_checks <== 0;
    component normalize = Normalize(k, p, 2 * p + 1);
    normalize.e <== if_else_beta_e.out;
    normalize.m <== m_alpha_left_shift.y + beta_m;
    normalize.skip_checks <== 0;
    component round_chk = RoundAndCheck(k, p, 2 * p + 1);
    round_chk.e <== normalize.e_out;
    round_chk.m <== normalize.m_out;

    // Assign final output values using If-Then-Else components
    component if_else_e_result = IfThenElse();
    if_else_e_result.cond <== skip_condition.out;
    if_else_e_result.L <== alpha_e;
    if_else_e_result.R <== round_chk.e_out;

    component if_else_m_result = IfThenElse();
    if_else_m_result.cond <== skip_condition.out;
    if_else_m_result.L <== alpha_m;
    if_else_m_result.R <== round_chk.m_out;

    // Set the output signals
    e_out <== if_else_e_result.out;
    m_out <== if_else_m_result.out;
}