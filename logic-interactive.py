import re

# ------------------------
# Expression Classes
# ------------------------
class Expr: pass

class Symbol(Expr):
    def __init__(self, name): self.name = name
    def __repr__(self): return self.name

class Not(Expr):
    def __init__(self, expr): self.expr = expr
    def __repr__(self): return f"(not {self.expr})"

class And(Expr):
    def __init__(self, left, right): self.left, self.right = left, right
    def __repr__(self): return f"({self.left} and {self.right})"

class Or(Expr):
    def __init__(self, left, right): self.left, self.right = left, right
    def __repr__(self): return f"({self.left} or {self.right})"

class Implies(Expr):
    def __init__(self, left, right): self.left, self.right = left, right
    def __repr__(self): return f"({self.left} implies {self.right})"

# ------------------------
# Parser for Nested Expressions
# ------------------------
class Parser:
    def __init__(self, text):
        self.tokens = re.findall(r'\w+|[()]', text)
        self.pos = 0

    def peek(self): return self.tokens[self.pos] if self.pos < len(self.tokens) else None
    def consume(self): tok = self.peek(); self.pos += 1; return tok

    def parse(self): return self.parse_implies()

    def parse_implies(self):
        left = self.parse_or()
        while self.peek() == 'implies':
            self.consume()
            right = self.parse_or()
            left = Implies(left, right)
        return left

    def parse_or(self):
        left = self.parse_and()
        while self.peek() == 'or':
            self.consume()
            right = self.parse_and()
            left = Or(left, right)
        return left

    def parse_and(self):
        left = self.parse_not()
        while self.peek() == 'and':
            self.consume()
            right = self.parse_not()
            left = And(left, right)
        return left

    def parse_not(self):
        if self.peek() == 'not':
            self.consume()
            return Not(self.parse_not())
        return self.parse_atom()

    def parse_atom(self):
        token = self.peek()
        if token == '(':
            self.consume()
            expr = self.parse_implies()
            if self.peek() != ')':
                raise ValueError("Mismatched parentheses")
            self.consume()
            return expr
        return Symbol(self.consume())

# ------------------------
# Knowledge Base
# ------------------------
class KnowledgeBase:
    def __init__(self):
        self.clear()

    def clear(self):
        self.facts_true = set()
        self.facts_false = set()
        self.symbol_desc = {}  # maps symbols -> narrative text
        self.rules = []  # list of (premise, conclusion)
        print("Knowledge base cleared.")

    # ------------------------
    # Tell: add facts or rules
    # ------------------------
    def tell(self, statement):
        if "=" in statement:  # define a symbol as true with description
            symbol, desc = map(str.strip, statement.split("=", 1))
            if symbol in self.facts_false:
                print(f"Contradiction detected: {symbol} is already known false.")
                return
            self.facts_true.add(symbol)
            self.symbol_desc[symbol] = desc
            print(f"Added fact: {symbol} = {desc}")
            self.forward_chain()
            return

        expr = Parser(statement).parse()

        if isinstance(expr, Implies):
            self.rules.append((expr.left, expr.right))
            print(f"Added rule: {expr}")
            self.forward_chain()
        else:
            if self._contradicts(expr, True):
                print(f"Contradiction detected: {expr}")
                return
            self._add_fact(expr, True)
            print(f"Added fact: {self._expr_to_str(expr)}")
            self.forward_chain()

    # ------------------------
    # Ask: evaluate with backward chaining and proof tree
    # ------------------------
    def ask(self, statement):
        expr = Parser(statement).parse()

        # Direct knowledge check first
        val = self._evaluate(expr)
        if val is True:
            print(f"True: {self._expr_to_str(expr)}")
            return
        elif val is False:
            print(f"False: {self._expr_to_str(expr)}")
            return

        # Backward chaining (with contradiction detection)
        val, proof = self._backward_chain(expr, set())
        if val is None:
            print(f"Unknown: {self._expr_to_str(expr)}")
        else:
            print(f"{'True' if val else 'False'} (proved): {self._expr_to_str(expr)}")
            print("Proof:\n" + self._format_proof(proof))

    # ------------------------
    # Forward Chaining
    # ------------------------
    def forward_chain(self):
        changed = True
        while changed:
            changed = False
            for premise, conclusion in self.rules:
                if self._evaluate(premise) is True:
                    if self._evaluate(conclusion) is not True:
                        if self._contradicts(conclusion, True):
                            print(f"Contradiction detected during inference: {self._expr_to_str(conclusion)}")
                            self._add_fact(conclusion, False)
                            continue
                        self._add_fact(conclusion, True)
                        changed = True

    # ------------------------
    # Backward Chaining with Contradiction Detection
    # ------------------------
    def _backward_chain(self, expr, visited):
        if repr(expr) in visited:
            return None, []
        visited.add(repr(expr))

        if isinstance(expr, Symbol):
            # Check for known facts
            if expr.name in self.facts_true:
                return True, [(expr, "Given as fact")]
            if expr.name in self.facts_false:
                return False, [(expr, "Contradiction: Known to be false")]

            # Try to prove via rules
            for premise, conclusion in self.rules:
                if self._equal(conclusion, expr):
                    val, proof = self._backward_chain(premise, visited)
                    if val is True:
                        return True, [(expr, f"Inferred from {self._expr_to_str(premise)} implies {self._expr_to_str(conclusion)}")] + proof
                    if val is False:
                        return False, [(expr, f"Cannot hold because {self._expr_to_str(premise)} is false")] + proof

            return None, [(expr, "Unknown")]

        if isinstance(expr, Not):
            val, proof = self._backward_chain(expr.expr, visited)
            if val is True:
                return False, [(expr, f"Negation fails because {self._expr_to_str(expr.expr)} is true")] + proof
            if val is False:
                return True, [(expr, f"Negation succeeds because {self._expr_to_str(expr.expr)} is false")] + proof
            return None, [(expr, f"Unknown because {self._expr_to_str(expr.expr)} is unknown")] + proof

        if isinstance(expr, And):
            l_val, l_proof = self._backward_chain(expr.left, visited)
            r_val, r_proof = self._backward_chain(expr.right, visited)
            if l_val is False or r_val is False:
                return False, [(expr, "One conjunct false")] + l_proof + r_proof
            if l_val is True and r_val is True:
                return True, [(expr, "Both conjuncts true")] + l_proof + r_proof
            return None, [(expr, "One conjunct unknown")] + l_proof + r_proof

        if isinstance(expr, Or):
            l_val, l_proof = self._backward_chain(expr.left, visited)
            r_val, r_proof = self._backward_chain(expr.right, visited)
            if l_val is True or r_val is True:
                return True, [(expr, "One disjunct true")] + l_proof + r_proof
            if l_val is False and r_val is False:
                return False, [(expr, "Both disjuncts false")] + l_proof + r_proof
            return None, [(expr, "One disjunct unknown")] + l_proof + r_proof

        if isinstance(expr, Implies):
            l_val, l_proof = self._backward_chain(expr.left, visited)
            r_val, r_proof = self._backward_chain(expr.right, visited)
            if l_val is True and r_val is False:
                return False, [(expr, "Contradiction: antecedent true and consequent false")] + l_proof + r_proof
            if l_val is False or r_val is True:
                return True, [(expr, "Implication satisfied")] + l_proof + r_proof
            return None, [(expr, "Implication unknown")] + l_proof + r_proof

    def _format_proof(self, proof):
        return "\n".join([f"- {self._expr_to_str(expr)}: {reason}" for expr, reason in proof])

    # ------------------------
    # Helpers
    # ------------------------
    def _expr_to_str(self, expr):
        """Convert expression to string with narrative if available."""
        if isinstance(expr, Symbol):
            if expr.name in self.symbol_desc:
                return f"{expr.name} = {self.symbol_desc[expr.name]}"
            return expr.name
        if isinstance(expr, Not):
            return f"not {self._expr_to_str(expr.expr)}"
        if isinstance(expr, And):
            return f"({self._expr_to_str(expr.left)} and {self._expr_to_str(expr.right)})"
        if isinstance(expr, Or):
            return f"({self._expr_to_str(expr.left)} or {self._expr_to_str(expr.right)})"
        if isinstance(expr, Implies):
            return f"({self._expr_to_str(expr.left)} implies {self._expr_to_str(expr.right)})"
        return str(expr)

    def _add_fact(self, expr, truth):
        if isinstance(expr, Symbol):
            if truth: self.facts_true.add(expr.name)
            else: self.facts_false.add(expr.name)
        elif isinstance(expr, Not):
            self._add_fact(expr.expr, not truth)
        elif isinstance(expr, And):
            if truth:
                self._add_fact(expr.left, True)
                self._add_fact(expr.right, True)

    def _contradicts(self, expr, truth):
        if isinstance(expr, Symbol):
            return (truth and expr.name in self.facts_false) or \
                   (not truth and expr.name in self.facts_true)
        if isinstance(expr, Not):
            return self._contradicts(expr.expr, not truth)
        if isinstance(expr, And):
            return self._contradicts(expr.left, truth) or self._contradicts(expr.right, truth)
        return False

    def _evaluate(self, expr):
        if isinstance(expr, Symbol):
            if expr.name in self.facts_true: return True
            if expr.name in self.facts_false: return False
            return None
        if isinstance(expr, Not):
            val = self._evaluate(expr.expr)
            return None if val is None else not val
        if isinstance(expr, And):
            l, r = self._evaluate(expr.left), self._evaluate(expr.right)
            if l is False or r is False: return False
            if l is True and r is True: return True
            return None
        if isinstance(expr, Or):
            l, r = self._evaluate(expr.left), self._evaluate(expr.right)
            if l is True or r is True: return True
            if l is False and r is False: return False
            return None
        if isinstance(expr, Implies):
            l, r = self._evaluate(expr.left), self._evaluate(expr.right)
            if l is True and r is False: return False
            if l is False or r is True: return True
            return None

    def _equal(self, a, b):
        return repr(a) == repr(b)

# ------------------------
# Interactive Shell
# ------------------------
def interactive_system():
    kb = KnowledgeBase()
    while True:
        cmd = input("\n> ").strip()
        if cmd == "exit": break
        if cmd == "clear": kb.clear()
        elif cmd.startswith("tell "): kb.tell(cmd[5:].strip())
        elif cmd.startswith("ask "): kb.ask(cmd[4:].strip())
        else: print("Use: tell <stmt>, ask <stmt>, clear, exit")

if __name__ == "__main__":
    interactive_system()

