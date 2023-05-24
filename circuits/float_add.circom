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
    signal input in;
    signal output out;

    // TODO

    //generate var bits of b
    signal bits[b];
    component check = IsZero();
    var sum = 0;

    //iterate over all the bits
    // Now, contrain each bit to be 0 or 1.
    for(var i=0; i<b; i++) {
        //modify the ith bit so its
        bits[i] <-- 1 & (in >> i) ;
        // Use `===` to enforce a rank-1 constraint (R1C) on signals.
        bits[i] * (1 - bits[i]) === 0;
    }

    
    //calc the sum of the input 
    for (var i = 0; i<b; i++){
        ///from num2bits
        sum = sum +(1 << i)*bits[i];
    }

    
    //check if sum is same as input and copy output
    sum - in ==> check.in;
    check.out ==> out;
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
 * Right-shifts `x` by `shift` bits to output `y`, where `shift` is a public circuit parameter.
 */
template RightShift(shift) {
    signal input x;
    signal output y;
    // TODO

    component check = LessThan(shift);
    //set signal result to input shifted by shift.
    signal result <-- x >> shift;

    //check that the shifted input is less than the original
    x-(result*(1<<shift)) ==> check.in[0];
    (1<<shift) ==>  check.in[1];

    //check that the output is less than
    check.out === 1;

    //set output to the result of a logical shift
    y <== result;
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
    component right_shift = RightShift(round_amt);
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

    //enforce shift is in correct bounds
    assert(skip_checks || (0 <= shift && shift < shift_bound));

    component checkEqualArray[shift_bound];
    var result = 0;
    // log("this is shift", shift);

    //for every element in the shiftbound
    for (var i = 0; i<shift_bound; i++) {
        //create array
        checkEqualArray[i]=IsEqual();
        
        //check when we need to shift.
        checkEqualArray[i].in[0] <== i;
        checkEqualArray[i].in[1] <== shift;

        //set the result to how much we need to push
        //should only be 1 number cant termnate early bc error in constraint gen phase.
        result = result + checkEqualArray[i].out * (1<<i);
        // log(result);
    }

    //set y as x shifted by the result
    y <== x * result;
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

    // TODO

    //check conditions
    component condCheck = IfThenElse();
    condCheck.cond <== skip_checks;
    //set to zero if skip checks is enabled
    condCheck.L <== 0;

    component inAsBits = Num2Bits(b);
    inAsBits.in <== in;


    /*
     * prod[i] === prod[i+1] * (1 - inBits.bits[i+1]), which is the suffix product of 'in'
     */

    signal location[b];
    //base case
    location[b-1] <== 1;
    //elem is not prev inbit
    for (var i=b-2; i >= 0; i--) {
        location[i] <== location[i+1] * (1-inAsBits.bits[i+1]);
    }
    //location 0 after this should hold the most significant bit

    // signal test[b];
    // test[0] <== 1;
    // for (var i = 1; i < b; i++){
    //     test[i] <== test[i-1] * (1 - inAsBits.bits[i-1]);
    // }
    // for(var i = 0; i< b; i ++){
    //     log("this is the elems", test[b-i], move[i], i);
    // }

    for (var i = 0; i < b; i ++ ){
        //set one_hot bits from input
        one_hot[i] <== inAsBits.bits[i] * location[i];
    }

    condCheck.R <== location[0] * (1-inAsBits.bits[0]);
    //ensure that we are in valid case
    condCheck.out === 0;
}

/*
 * Normalizes the input floating-point number.
 * The input is a floating-point number with a `k`-bit exponent `e` and a `P`+1-bit *unnormalized* mantissa `m` with precision `p`, where `m` is assumed to be non-zero.
 * The output is a floating-point number representing the same value with exponent `e_out` and a *normalized* mantissa `m_out` of `P`+1-bits and precision `P`.
 * Enforces that `m` is non-zero as a zero-value can not be normalized.
 * If `skip_checks` = 1, then we don't care about the output and the non-zero constraint is not enforced.
 */
template Normalize(k, p, P) {
    signal input e;
    signal input m;
    signal input skip_checks;
    signal output e_out;
    signal output m_out;
    assert(P > p);

    // TODO

    //calculate the MSNZB 
    component msnzb = MSNZB(P+1);
    //input the mantisa and the skip_checks
    msnzb.in <== m;
    msnzb.skip_checks <== skip_checks;
    //MSNZB should verify the skip_checks condition. 
    
    //normalization elements for the exponent and mantisa
    var eNorm = 0;
    var mNorm = 0;

    //iterate over all P+1 bits for output
    for (var i = 0; i<P+1; i++) {
        //set norm elems
        mNorm = mNorm + msnzb.one_hot[i]*(1<<(P-i));
        eNorm = eNorm + msnzb.one_hot[i]*i;
    }

    //set output
    m_out <== mNorm * m;
    e_out <== e + eNorm - p;
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

    // TODO

    component check1;
    component check2;

    //check if first flaot is well formed
    check1 = CheckWellFormedness(k, p);
    check1.e <== e[0];
    check1.m <== m[0];

    //check if second float is well formed
    check2 = CheckWellFormedness(k, p);
    check2.e <== e[1];
    check2.m <== m[1];
    
    

    /*
     * comparing e[1] || m[1] against e[2] || m[2] suffices to compare magnitudes.
     */

    component checkLessThan = LessThan(k+p+1);
    component checkExponentLT = LessThan(k);
    component exponetSwitch = Switcher(); 
    component mantissaSwitcher = Switcher();
    //check if any are less than k+p+1
    checkLessThan.in[0] <== m[0] + e[0] * (1<<(p+1));
    checkLessThan.in[1] <== m[1] + e[1] * (1<<(p+1));



    //switch left and right if one based on if one is less than other
    exponetSwitch.sel <== checkLessThan.out;
    exponetSwitch.L <== e[0];
    exponetSwitch.R <== e[1];
    //set vars based on earlier components
    var firstExponent = exponetSwitch.outL;
    var secondExponent = exponetSwitch.outR;
    //calculate diffrence in exponent
    signal exponentDiff <== firstExponent - secondExponent;
    //check if exponent is greater than p+1
    checkExponentLT.in[0] <== p+1;
    checkExponentLT.in[1] <== exponentDiff;

    //check if the first exponent is nonZero
    component checkNonZero = IsZero();
    checkNonZero.in <== firstExponent;

    //combine prev 2 checks
    component validExponent = OR();
    validExponent.a <== checkExponentLT.out;
    validExponent.b <== checkNonZero.out;

    //switch left and right if one based on if one is less than other
    mantissaSwitcher.sel <== checkLessThan.out;
    mantissaSwitcher.L <== m[0];
    mantissaSwitcher.R <== m[1];
    //set vars based on earlier componenets
    var firstMantissa = mantissaSwitcher.outL;
    var secondMantissa = mantissaSwitcher.outR;

    //generate new values for the float addition 
        //generate the shift needed for the manitisa
    component getShift = IfThenElse();
    getShift.cond <== validExponent.out;
    getShift.L <== 0;
    getShift.R <== exponentDiff;

    //generate new input exponent
    component getInputExponent = IfThenElse();
    getInputExponent.cond <== validExponent.out;
    getInputExponent.L <== 1;
    getInputExponent.R <== secondExponent;

    //generate new input mantsa
    component getInputMantissa = IfThenElse();
    getInputMantissa.cond <== validExponent.out;
    getInputMantissa.L <== 1;
    getInputMantissa.R <== firstMantissa;



    //start computation
    component shiftFirstMantissa = LeftShift(p+2);
    shiftFirstMantissa.x <== getInputMantissa.out;
    shiftFirstMantissa.shift <== getShift.out;
    shiftFirstMantissa.skip_checks <== 0;

    //normalize shifted mantissa with new exponent
    component normalize = Normalize(k, p, 2*p+1);
    normalize.e <== getInputExponent.out;
    //add mantissas
    normalize.m <== secondMantissa + shiftFirstMantissa.y;
    normalize.skip_checks <== 0;

    //round and check the normalized calculated output
    component roundCheck = RoundAndCheck(k, p, 2*p+1);
    roundCheck.e <== normalize.e_out;
    roundCheck.m <== normalize.m_out;

    //choose which mantissa
    component getOutputMantissa = IfThenElse();
    getOutputMantissa.cond <== validExponent.out;
    getOutputMantissa.L <== firstMantissa;
    getOutputMantissa.R <== roundCheck.m_out;

    //choose which exponent for output
    component getOutputExponent = IfThenElse();
    getOutputExponent.cond <== validExponent.out;
    getOutputExponent.L <== firstExponent;
    getOutputExponent.R <== roundCheck.e_out;

    //set output vars
    e_out <== getOutputExponent.out;
    m_out <== getOutputMantissa.out;

}
