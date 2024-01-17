# Synthetic Programming Elicitation

## Usage
```sh
eudoxus --help
eudoxus sketch --help
eudoxus complete --help
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
pyenv exec pre-commit run --all-files --show-diff-on-failure
```
