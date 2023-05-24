const path = require("path");
const assert = require("chai").assert;
const wasm_tester = require("circom_tester").wasm;

describe("FP32Add", () => {
    var circ_file = path.join(__dirname, "circuits", "fp32_add.circom");
    var circ, num_constraints;

    before(async () => {
        circ = await wasm_tester(circ_file);
        await circ.loadConstraints();
        num_constraints = circ.constraints.length;
        var k = 8, p = 23;
        console.log("Float32 Add #Constraints:", num_constraints, "Expected:", 376);
    });

    it("case I test", async () => {
        const input = {
            "e": ["43", "5"],
            "m": ["11672136", "10566265"],
        };
        const witness = await circ.calculateWitness(input, 1);
        await circ.checkConstraints(witness);
        await circ.assertOut(witness, {"e_out": "43", "m_out": "11672136"});
    });

    it("case II test 1", async () => {
        const input = {
            "e": ["104", "106"],
            "m": ["12444445", "14159003"],
        };
        const witness = await circ.calculateWitness(input);
        await circ.checkConstraints(witness);
        await circ.assertOut(witness, {"e_out": "107", "m_out": "8635057"});
    });

    it("case II test 2", async () => {
        const input = {
            "e": ["176", "152"],
            "m": ["13291872", "15152854"],
        };
        const witness = await circ.calculateWitness(input);
        await circ.checkConstraints(witness);
        await circ.assertOut(witness, {"e_out": "176", "m_out": "13291873"});
    });

    it("case II test 3", async () => {
        const input = {
            "e": ["142", "142"],
            "m": ["13291872", "13291872"],
        };
        const witness = await circ.calculateWitness(input);
        await circ.checkConstraints(witness);
        await circ.assertOut(witness, {"e_out": "143", "m_out": "13291872"});
    });

    it("one input zero test", async () => {
        const input = {
            "e": ["0", "43"],
            "m": ["0", "10566265"],
        };
        const witness = await circ.calculateWitness(input);
        await circ.checkConstraints(witness);
        await circ.assertOut(witness, {"e_out": "43", "m_out": "10566265"});
    });

    it("both inputs zero test", async () => {
        const input = {
            "e": ["0", "0"],
            "m": ["0", "0"],
        };
        const witness = await circ.calculateWitness(input);
        await circ.checkConstraints(witness);
        await circ.assertOut(witness, {"e_out": "0", "m_out": "0"});
    });

    it("should fail - exponent zero but mantissa non-zero", async () => {
        const input = {
            "e": ["0", "0"],
            "m": ["0", "10566265"],
        };
        try {
            const witness = await circ.calculateWitness(input);
        } catch (e) {
            return 0;
        }
        assert.fail("should have thrown an error");
    });

    it("should fail - mantissa >= 2^{p+1}", async () => {
        const input = {
            "e": ["0", "43"],
            "m": ["0", "16777216"],
        };
        try {
            const witness = await circ.calculateWitness(input);
        } catch (e) {
            return 0;
        }
        assert.fail("should have thrown an error");
    });

    it("should fail - mantissa < 2^{p}", async () => {
        const input = {
            "e": ["0", "43"],
            "m": ["0", "6777216"],
        };
        try {
            const witness = await circ.calculateWitness(input);
        } catch (e) {
            return 0;
        }
        assert.fail("should have thrown an error");
    });

    it("should fail - exponent >= 2^k", async () => {
        const input = {
            "e": ["0", "256"],
            "m": ["0", "10566265"],
        };
        try {
            const witness = await circ.calculateWitness(input);
        } catch (e) {
            return 0;
        }
        assert.fail("should have thrown an error");
    });

    it("should fail - wrong output for case I", async () => {
        const input = {
            "e": ["43", "5"],
            "m": ["11672136", "10566265"],
        };
        try {
            const witness = await circ.calculateWitness(input);
            await circ.assertOut(witness, {"e_out": "42", "m_out": "11672136"});
        } catch (e) {
            return 0;
        }
        assert.fail("should have thrown an error");
    });

    it("should fail - wrong output for case II", async () => {
        const input = {
            "e": ["104", "106"],
            "m": ["12444445", "14159003"],
        };
        try {
            const witness = await circ.calculateWitness(input);
            await circ.assertOut(witness, {"e_out": "107", "m_out": "8635056"});
        } catch (e) {
            return 0;
        }
        assert.fail("should have thrown an error");
    });
});

describe("FP64Add", () => {
    var circ_file = path.join(__dirname, "circuits", "fp64_add.circom");
    var circ, num_constraints;

    before(async () => {
        circ = await wasm_tester(circ_file);
        await circ.loadConstraints();
        num_constraints = circ.constraints.length;
        console.log("Float64 Add #Constraints:", num_constraints, "Expected:", 765);
    });

    it("case I test", async () => {
        const input = {
            "e": ["1122", "1024"],
            "m": ["7807742059002284", "7045130465601185"],
        };
        const witness = await circ.calculateWitness(input, 1);
        await circ.checkConstraints(witness);
        await circ.assertOut(witness, {"e_out": "1122", "m_out": "7807742059002284"});
    });

    it("case II test 1", async () => {
        const input = {
            "e": ["1056", "1053"],
            "m": ["8879495032259305", "5030141535601637"],
        };
        const witness = await circ.calculateWitness(input);
        await circ.checkConstraints(witness);
        await circ.assertOut(witness, {"e_out": "1057", "m_out": "4754131362104755"});
    });

    it("case II test 2", async () => {
        const input = {
            "e": ["1035", "982"],
            "m": ["4804509148660890", "8505192799372177"],
        };
        const witness = await circ.calculateWitness(input);
        await circ.checkConstraints(witness);
        await circ.assertOut(witness, {"e_out": "1035", "m_out": "4804509148660891"});
    });

    it("case II test 3", async () => {
        const input = {
            "e": ["982", "982"],
            "m": ["8505192799372177", "8505192799372177"],
        };
        const witness = await circ.calculateWitness(input);
        await circ.checkConstraints(witness);
        await circ.assertOut(witness, {"e_out": "983", "m_out": "8505192799372177"});
    });

    it("one input zero test", async () => {
        const input = {
            "e": ["0", "982"],
            "m": ["0", "8505192799372177"],
        };
        const witness = await circ.calculateWitness(input);
        await circ.checkConstraints(witness);
        await circ.assertOut(witness, {"e_out": "982", "m_out": "8505192799372177"});
    });

    it("both inputs zero test", async () => {
        const input = {
            "e": ["0", "0"],
            "m": ["0", "0"],
        };
        const witness = await circ.calculateWitness(input);
        await circ.checkConstraints(witness);
        await circ.assertOut(witness, {"e_out": "0", "m_out": "0"});
    });

    it("should fail - exponent zero but mantissa non-zero", async () => {
        const input = {
            "e": ["0", "0"],
            "m": ["0", "8505192799372177"],
        };
        try {
            const witness = await circ.calculateWitness(input);
        } catch (e) {
            return 0;
        }
        assert.fail("should have thrown an error");
    });

    it("should fail - mantissa < 2^{p}", async () => {
        const input = {
            "e": ["0", "43"],
            "m": ["0", "16777216"],
        };
        try {
            const witness = await circ.calculateWitness(input);
        } catch (e) {
            return 0;
        }
        assert.fail("should have thrown an error");
    });

    it("should fail - wrong output for case I", async () => {
        const input = {
            "e": ["1122", "1024"],
            "m": ["7807742059002284", "7045130465601185"],
        };
        try {
            const witness = await circ.calculateWitness(input);
            await circ.assertOut(witness, {"e_out": "1122", "m_out": "7807742059002285"});
        } catch (e) {
            return 0;
        }
        assert.fail("should have thrown an error");
    });

    it("should fail - wrong output for case II", async () => {
        const input = {
            "e": ["1056", "1053"],
            "m": ["8879495032259305", "5030141535601637"],
        };
        try {
            const witness = await circ.calculateWitness(input);
            await circ.assertOut(witness, {"e_out": "1057", "m_out": "4754131362104754"});
        } catch (e) {
            return 0;
        }
        assert.fail("should have thrown an error");
    });
});
