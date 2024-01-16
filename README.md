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
brew install pyenv
pyenv install 3.11.7
pyenv local 3.11.7
pip install pipx
pipx install pre-commit
```

### Installation (for development)
```sh
pipx install -e .
```

## Testing
```sh
pipx run tox
```

## Formatting
```sh
pre-commit run --all-files --show-diff-on-failure
```
