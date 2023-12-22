from uclid_lm_ir import gpt4_write_code

task = """
write a transition system that models a counter that counts up to 10 and then
resets to 0.
"""

code = gpt4_write_code(task)

print(code)
