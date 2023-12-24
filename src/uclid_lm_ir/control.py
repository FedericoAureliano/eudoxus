def induction(k=1):
    return f"induction({k});\ncheck;\nprint_results();\n"


proof_by_induction = induction
Induction = induction


def bmc(k=1):
    return f"bmc({k});\ncheck;\nprint_results();\n"


bounded_model_checking = bmc
BMC = bmc
Bounded_model_checking = bmc
Unroll = bmc
unroll = bmc
