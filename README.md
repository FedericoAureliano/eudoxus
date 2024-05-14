# eudoxus: [UCLID5](https://github.com/uclid-org/uclid) text-to-code tool

"Eudoxus was probably the source for most of book V of Euclid's Elements." -
[Wikipedia](https://en.wikipedia.org/wiki/Eudoxus_of_Cnidus)

## Install
```sh
pip3 install .
```

## Usage
```
 Usage: eudoxus [OPTIONS] TASK

╭─ Arguments ───────────────────────────────────────────────────────────────────╮
│ *    task      PATH  [default: None] [required]                               │
╰───────────────────────────────────────────────────────────────────────────────╯
╭─ Options ─────────────────────────────────────────────────────────────────────╮
│ --language                        [python|uclid]  [default: uclid]            │
│ --output                          PATH            [default: None]             │
│ --iterations                      INTEGER         [default: 2]                │
│ --inference     --no-inference                    [default: inference]        │
│ --remind        --no-remind                       [default: remind]           │
│ --help                                            Show this message and exit. │
╰───────────────────────────────────────────────────────────────────────────────╯
```

Set `iterations` to any value less than 1 to just do repair.

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
