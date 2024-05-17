from typing import Dict, List

import eudoxus.ast.expression as e
import eudoxus.ast.module as m
import eudoxus.ast.statement as s
import eudoxus.ast.type as t
from eudoxus.ast.node import Identifier, Node, Position
from eudoxus.repair.interface import Checker


class Scope:
    def __init__(self) -> None:
        self.map = {}

    def add(self, name: str, pos: Position) -> None:
        if name not in self.map:
            self.map[name] = []
        self.map[name].append(pos)

    def get(self, name: str) -> List[Position]:
        return self.map.get(name, [])

    def __repr__(self) -> str:
        return str(self.map)


class ScopeStack:
    def __init__(self) -> None:
        self.stack = []

    def add(self, name: str, pos: Position) -> None:
        self.stack[-1].add(name, pos)

    def exists(self, name: str) -> bool:
        for scope in reversed(self.stack):
            if name in scope.map:
                return True
        return False

    def rename(self, name: str) -> str | None:
        count = 0
        for scope in reversed(self.stack):
            if name in scope.map:
                count += 1

        if count <= 0:
            return None

        if count == 1:
            return name

        new_name = f"{name}{count - 2}"
        while self.exists(new_name):
            count += 1
            new_name = f"{name}{count - 2}"

        return new_name

    def enter_scope(self) -> None:
        self.stack.append(Scope())

    def exit_scope(self) -> None:
        self.stack.pop()

    def __repr__(self) -> str:
        return str(self.stack)


class ScopeChecker(Checker):
    """
    Rename all the variables so that they are unique in each scope and declare
    the ones that need declaring. For example,
    ```
    var x: boolean;
    assert (forall (x: integer) :: x = 0);
    assert (forall (x: boolean) :: x);
    ```
    becomes
    ```
    var x: boolean;
    assert (forall (x1: integer) :: x1 = 0);
    assert (forall (x1: boolean) :: x1);
    ```
    """

    def enter_scope(self, node):
        match node:
            case m.Module(_, _, _, _, _, _, _, _, _, _):
                self.scopes.enter_scope()
            case s.LocalDecl(position, target, _) | s.InputDecl(
                position, target, _
            ) | s.SharedDecl(position, target, _) | s.OutputDecl(position, target, _):
                self.scopes.add(target.name, position)
            case e.Forall(position, bound, _, _) | e.Exists(position, bound, _, _):
                self.scopes.enter_scope()
                self.scopes.add(bound.name, position)
                new_name = self.scopes.rename(bound.name)
                if new_name != bound.name:
                    self.rewrites[bound.position] = Identifier(bound.position, new_name)
            case e.FunctionApplication(position, target, args):
                new_name = self.scopes.rename(target.name)
                if new_name is None:
                    self.vars_to_declare.add(target.name)
                elif new_name != target.name:
                    new_id = Identifier(target.position, new_name)
                    new_func = e.FunctionApplication(position, new_id, args)
                    self.rewrites[position] = new_func
            case s.Havoc(position, target):
                new_name = self.scopes.rename(target.name)
                if new_name is None:
                    self.vars_to_declare.add(target.name)
                elif new_name != target.name:
                    new_id = Identifier(target.position, new_name)
                    new_havoc = s.Havoc(position, new_id)
                    self.rewrites[position] = new_havoc

    def exit_scope(self, node):
        match node:
            case m.Module(_, _, _, _, _, _, _, _, _, _):
                self.scopes.exit_scope()
            case e.Forall(_, _, _, _) | e.Exists(_, _, _, _):
                self.scopes.exit_scope()

    def check(self, modules: List[m.Module]) -> List[Dict[Position, Node]]:
        self.position = -3000

        def new_pos():
            self.position -= 1
            return Position(self.position)

        self.scopes = ScopeStack()

        self.rewrites = {}

        for module in modules:
            self.vars_to_declare = set()
            module.traverse(self.enter_scope, self.exit_scope)

            var_block = module.locals
            pv = var_block.position
            new_var_decls = []
            for var_name in self.vars_to_declare:
                new_var_decl = s.LocalDecl(
                    new_pos(), Identifier(new_pos(), var_name), t.HoleType(new_pos())
                )
                new_var_decls.append(new_var_decl)
            new_var_block = s.Block(new_pos(), new_var_decls + var_block.statements)
            self.rewrites[pv] = new_var_block

        return [self.rewrites]
