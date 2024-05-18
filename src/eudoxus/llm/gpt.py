import os

from openai import OpenAI


def chat(prompt, engine):
    if os.environ["OPENAI_API_KEY"]:
        client = OpenAI(api_key=os.environ["OPENAI_API_KEY"])
    else:
        raise ValueError("No OPENAI_API_KEY")
    response = client.chat.completions.create(
        model=engine, messages=[{"role": "user", "content": prompt}]
    )
    return response.choices[0].message.content.strip()
