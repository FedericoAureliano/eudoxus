def extract_code(output) -> str:
    """Extracts the code from the LLM response."""
    output = output.rstrip()
    output = "```python\n" + output

    # replace any occurrences of "``````" with "```"
    output = output.replace("``````", "```")

    end_index = output.rfind("```")
    before_start = output.rfind("```", 0, end_index)
    # find the newline after the index
    start_index = output.find("\n", before_start + 1)

    # extract the code
    code = output[start_index:end_index]
    # remove trailing new lines
    code = code.rstrip()

    return code
