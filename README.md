# eudoxus: [UCLID5](https://github.com/uclid-org/uclid) text-to-code tool

"Eudoxus was probably the source for most of book V of Euclid's Elements." - [Wikipedia](https://en.wikipedia.org/wiki/Eudoxus_of_Cnidus)

## Usage
The main way to use eudoxus is through the `synthesize` command.
```
 Usage: eudoxus synthesize [OPTIONS] TASK

 Synthesize a complete UCLID5 model from a natural language description.

╭─ Arguments ────────────────────────────────────────────────────────────────────────────────╮
│ *    task      TEXT  Description of the desired UCLID5 code in natural language [required] │
╰────────────────────────────────────────────────────────────────────────────────────────────╯
╭─ Options ──────────────────────────────────────────────────────────────────────────────────╮
│ --examples     PATH     Directory with example UCLID5 files to use for RAG [default: None] │
│ --neighbours   INTEGER  Number of neighbours to consider for RAG [default: 1]              │
│ --help                  Show this message and exit.                                        │
╰────────────────────────────────────────────────────────────────────────────────────────────╯
```

So, for example, you can run `eudoxus synthesize "model a fibonnaci sequence"`.

You may also find `sketch`, `fill`, or `add-to-tests` useful, depending on your needs.
```sh
eudoxus sketch --help
eudoxus fill --help
eudoxus add-to-tests --help # Note: this command is hidden
```

## Building

### Requirements (for MacOS)
```sh
export OPENAI_API_KEY='<YOUR OPENAI API KEY GOES HERE>'
brew install pyenv
pyenv install 3.11.7
pyenv local 3.11.7
pyenv exec pip install pre-commit
pyenv exec pre-commit install
```

### Installation (for development)
```sh
pyenv exec pip install -e . # remove -e if not for development
```

## Testing
```sh
pyenv exec tox
open htmlcov/index.html # to see coverage report
```

## Formatting
```sh
pre-commit run --all-files --show-diff-on-failure
```

## Language Support
The goal is to support most of [UCLID5](https://github.com/uclid-org/uclid). Currently we do not support:
- function definitions,
- procedure declarations or calls,
- finite quantifiers,
- groups,
- hyperproperties,
- linear temporal logic,
- multiple init or next blocks in the same module, or
- imports.
