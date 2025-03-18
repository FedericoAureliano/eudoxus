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


def chat_constrained(system_prompt, user_task, base_class):
    client = OpenAI()
    completion = client.beta.chat.completions.parse(
        model="gpt-4o-2024-08-06",
        messages=[
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": user_task},
        ],
        response_format=base_class,
    )

    suggestions_parsed = completion.choices[0].message.parsed
    # print("type parsed: ", type(suggestions_parsed))

    return suggestions_parsed
