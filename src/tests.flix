def assert(b: Bool): Unit \ IO = if (not b) println("Boolean assertion failed") else ()
def assertEq(x: a, y: a):  Unit \ IO with Eq[a], ToString[a] = 
    if (x != y) println("Assertion error:\n - Expected: ${x}\n - Actual: ${y}")
    else ()
def assertNeq(x: a, y: a):  Unit \ IO with Eq[a], ToString[a] = 
    if (x == y) println("Assertion error:\n - Expected: ${x}\n - Actual: ${y}")
    else ()

def dumbTest(): Unit \ IO = {
    let cnf = Map#{ 'S' => Set#{ CNFProd.Terminal(0), CNFProd.NonTerminal('S', 'S') }};

    assertEq(getVarsWith(CNFProd.Terminal(0), cnf), Set#{ 'S' });
    assertEq(getVarsWith(CNFProd.Terminal(1), cnf), Set.empty());

    assertEq(derivableFromCNF(0 :: Nil, cnf), Set#{ 'S' });
    assertEq(derivableFromCNF(0 :: 0 :: 0 :: 0 :: 1 :: Nil, cnf), Set.empty());

    assertEq(Set#{ CNFTree.Leaf('S', 0) }, parseCNF(0 :: Nil, cnf));
    assertEq(Set#{ 
        CNFTree.Node('S', 
            CNFTree.Leaf('S', 0),
            CNFTree.Leaf('S', 0)
        )
    }, parseCNF(0 :: 0 :: Nil, cnf))
}

def bracketsTest(): Unit \ IO = {
    let cnf: CNFGrammar[Char, Char] = 
        Map#{
            'S' => Set#{ CNFProd.NonTerminal('L', 'A'), CNFProd.NonTerminal('L', 'R'), CNFProd.NonTerminal('S', 'S')},
            'A' => Set#{ CNFProd.NonTerminal('S', 'R') },
            'L' => Set#{ CNFProd.Terminal('(') },
            'R' => Set#{ CNFProd.Terminal(')') } 
        };

    let member = (str: String, var: Char) -> Set.memberOf(var, derivableFromCNF(String.toList(str), cnf));
    assert(member("()", 'S'));
    assert(member("(()(()()))", 'S'));
    assert(member("()()((((())())()))()", 'S'));
    assert(member("()((()())()())", 'S'));

    assert(not member("())", 'S'));
    assert(not member(")()", 'S'));
    assert(not member(")", 'S'));
    assert(not member("(((()(())))))", 'S'));

    assertEq(derivableFromCNF(String.toList(""), cnf), Set.empty());
    assertEq(Set#{ CNFTree.Leaf('L', '(')}, parseCNF('(' :: Nil, cnf));
    assertEq(Set#{ CNFTree.Leaf('R', ')')}, parseCNF(')' :: Nil, cnf));
    assertEq(Set#{ CNFTree.Node('S', CNFTree.Leaf('L', '('), CNFTree.Leaf('R', ')')) }, parseCNF(String.toList("()"), cnf));

    let leaf = (v, t) -> CNFTree.Leaf(v, t);
    let node = (v, l, r) -> CNFTree.Node(v, l, r);

    assert(parseCNF(String.toList("(()())"), cnf) |> Set.memberOf(
        node('S',
            leaf('L', '('),
            node('A', 
                node('S', 
                    node('S', 
                        leaf('L', '('),
                        leaf('R', ')')
                    ),
                    node('S', 
                        leaf('L', '('),
                        leaf('R', ')')
                    )
                ),
                leaf('R', ')')
            )
        )
    ))
}