from eudoxus.dfy.ast.built_in.abs import AbsModule, abs_src
from eudoxus.dfy.ast.built_in.set import SetModule, set_src
from eudoxus.dfy.ast.built_in.sum import SumModule, sum_src

built_ins = {"sum": SumModule, "set": SetModule, "abs": AbsModule}
built_in_src = {-1: sum_src, -2: set_src, -3: abs_src}
