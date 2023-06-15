# terminates, proves as expected
manual_pass_sat:
	cbmc quantifiers_manual_pass.c

# terminates, fails as expected
manual_fail_overflow_sat:
	cbmc quantifiers_manual_fail_overflow.c

# terminates, proves as expected
manual_pass_smt2:
	cbmc --smt2 quantifiers_manual_pass.c

# terminates, fails as expected
manual_fail_overflow_smt2:
	cbmc --smt2 quantifiers_manual_fail_overflow.c

# terminates, ignored quantifiers warning, spurious failure
auto_pass_sat:
	cbmc  quantifiers_auto_pass.c

# ignored quantifiers warning, cannot trust output (spurious failure)
auto_fail_overflow_sat:
	cbmc  quantifiers_auto_fail_overflow.c

# terminates, success as expected
auto_pass_smt2:
	cbmc --smt2 quantifiers_auto_pass.c

# runs forever
auto_fail_overflow_smt2:
	cbmc --smt2 quantifiers_auto_fail_overflow.c
