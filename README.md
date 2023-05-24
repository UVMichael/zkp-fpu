# Overview
This project goes over Writing and Proving Arithmetic Circuits using circom and snarkjs. This project translates the floating point arithmetic outlined in The `src/` directory has a python program `float_add.py` that implements the floating-point addition logic. Into a ZKP circuit writen at `float_add.circom`. this ciruit as a optimal amount of contstrains for subpart of the floating point arithmetic calculation. There is also  two files `proof.json` and `verification_key.json` which are a `Groth16` proof that proves $7 \times 17 \times 19 = 2261$ using the `SmallOddFactorization` circuit implemented in `circuits/example.circom` and give an example on how to prove and arithmetic circuit.

## Setup

1. Install [nodejs](https://nodejs.org/en/download/) (includes `npm`).
2. Install `circom` following this [installation guide](https://docs.circom.io/getting-started/installation/). Once installed, ensure that you're using the correct version of `circom` by running `circom --version`. You should see `circom compiler 2.1.4` or later.
3. Install `snarkjs`: run `npm install -g snarkjs@latest`.
4. Install the `mocha test runner`: run `npm install -g mocha`.
5. Run `npm install` in the same directory as this readme to install the dependencies for this assignment.
6. Run `mocha test` 
