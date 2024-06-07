# eudoxus: [UCLID5](https://github.com/uclid-org/uclid) text-to-code tool

"Eudoxus was probably the source for most of book V of Euclid's Elements." -
[Wikipedia](https://en.wikipedia.org/wiki/Eudoxus_of_Cnidus)

---

Eudoxus is based on [Synthetic Programming Elicitation and Repair for Text-to-Code in Very Low-Resource Programming Languages](https://arxiv.org/abs/2406.03636). For a complete example run of the tool, see [`docs/results/eudoxus-gpt35/ls-ex3_13.txt`](docs/results/eudoxus-gpt35/ls-ex3_13.txt).

## Recommended Install
```sh
git clone https://github.com/FedericoAureliano/eudoxus.git
cd eudoxus
python3.11 -m venv .venv
source .venv/bin/activate
pip3 install .
```

## Usage
```
 Usage: eudoxus [OPTIONS] TASK

╭─ Arguments ──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────╮
│ *    task      PATH  [default: None] [required]                                                                                      │
╰──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────╯
╭─ Options ────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────╮
│ --language                        [python|uclid]                               [default: uclid]                                      │
│ --model                           [gpt-4-turbo-2024-04-09|gpt-3.5-turbo-0125]  [default: gpt-4-turbo-2024-04-09]                     │
│ --output                          PATH                                         [default: None]                                       │
│ --iterations                      INTEGER                                      [default: 2]                                          │
│ --inference     --no-inference                                                 [default: inference]                                  │
│ --remind        --no-remind                                                    [default: remind]                                     │
│ --help                                                                         Show this message and exit.                           │
╰──────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────────╯
```

To do anything other than repair, [you must have an OpenAI API Key in your ‘OPENAI_API_KEY’ environment variable](https://help.openai.com/en/articles/5112595-best-practices-for-api-key-safety). Set `iterations` to any value less than one to just do repair. The examples folder contains reapir input/output pairs. For example, running `eudoxus examples/arithmetic.input.py --iterations 0` should print out code equivalent to that in `examples/arithmetic.output.ucl`.

## Development

### Virtual Environment
```sh
python3.11 -m venv .venv
source .venv/bin/activate
# deactivate (for exiting virtual environment)
```

### Requirements (MacOS)
```sh
pip3 install pre-commit
pre-commit install
pip3 install "tox<4"
```

### Install
```sh
pip3 install -e .
```

### Testing
```sh
tox
open htmlcov/index.html # to see coverage report
```

### Formatting
```sh
pre-commit run --all-files --show-diff-on-failure
```
