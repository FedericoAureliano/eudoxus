# eudoxus: [UCLID5](https://github.com/uclid-org/uclid) text-to-code tool

"Eudoxus was probably the source for most of book V of Euclid's Elements." -
[Wikipedia](https://en.wikipedia.org/wiki/Eudoxus_of_Cnidus)

## Install
```sh
pip3 install .
```

## Usage
```
 Usage: eudoxus [OPTIONS] SRC

╭─ Arguments ─────────────────────────────────────────────────────────────────╮
│ *    src      PATH  [default: None] [required]                              │
╰─────────────────────────────────────────────────────────────────────────────╯
╭─ Options ───────────────────────────────────────────────────────────────────╮
│ --language                  [python|uclid]  [default: Language.python]      │
│ --output                    PATH            [default: None]                 │
│ --check       --no-check                    [default: check]                │
│ --help                                      Show this message and exit.     │
╰─────────────────────────────────────────────────────────────────────────────╯
```

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
