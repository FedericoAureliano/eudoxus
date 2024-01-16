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
pip install pipx
pipx install pre-commit
```

### Installation (for development)
```sh
pipx install -e . # remove -e if not for development
```

## Testing
```sh
pipx run tox
```

## Formatting
```sh
pre-commit run --all-files --show-diff-on-failure
```
