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

def testBrackets(): Unit \ IO = {
    let cfg: Grammar[Char, Char] = Map#{
        'S' => Set#{ 
            Nil, 
            CFGChar.Alph('(') :: CFGChar.Var('S') :: CFGChar.Alph(')') :: Nil,
            CFGChar.Var('S') :: CFGChar.Var('S') :: Nil
        }
    };

    let deadcfg = (cfg |> removeLambdaProductions)#cfg |> removeUnitProductions;
    assert(deadcfg |> Map.forAll((_, prods) -> prods |> Set.forAll(prod -> not isUnitProduction(prod))));
    assert(deadcfg |> Map.forAll((_, prods) -> prods |> Set.forAll(prod -> not isLambdaProduction(prod))));

    let (cnf, _, _) = deadcfg |> deadGrammarToCNF;
    cnf |> Map.forEach((k, prods) -> prods |> Set.forEach(p -> println("${k}: ${p}")));

    let parseWord = (str: String) -> cnf |> parseCNF(String.toList(str)) |> Set.filter(t -> match t {
        case CNFTree.Leaf(0, _) => true
        case CNFTree.Node(0, _, _) => true
        case _ => false
    });

    assert(not (parseWord("()()((()())()(()))()") |> Set.isEmpty));
    // parseWord("()(()()())()") |> Set.forEach(println);
    ()
}

def convertParseTreeTest(): Unit \ IO = {
    let cfg = Map#{
        'E' => Set#{ 
            CFGChar.Var('E') :: CFGChar.Alph('+') :: CFGChar.Var('E') :: Nil,
            CFGChar.Var('E') :: CFGChar.Alph('*') :: CFGChar.Var('E') :: Nil,
            CFGChar.Alph('(') :: CFGChar.Var('E') :: CFGChar.Alph(')') :: Nil,

            // CFGChar.Alph('a') :: CFGChar.Var('A') :: Nil,
            CFGChar.Alph('a') :: Nil
        }
        // 'A' => Set#{
        //     CFGChar.Alph('a') :: CFGChar.Var('A') :: Nil,
        //     CFGChar.Alph('a') :: Nil
        // }
    };

    let (cnf, varmap, alphmap) = deadGrammarToCNF(cfg);
    println("CNF grammar: ");
    cnf |> Map.forEach((var, prod) -> println("${var}: ${prod}"));

    let cnftrees = cnf |> parseCNF(String.toList("a+a")) |> Set.filter(t -> match t { 
        case CNFTree.Node(0, _, _) => true
        case _ => false
    });

    println("Before: ");
    cnftrees |> Set.forEach(println);
    println("After: ");
    cnftrees |> Set.map(tree -> convertCNFToCFGParseTree(tree, varmap, alphmap)) 
        |> Set.forEach(println);
    ()
}

def arithmeticTest(): Unit \ IO = {
    def eval(tree: CFGTree[Char, Char]): Int32\IO = match tree {
        case CFGTree.Node('S', CFGTree.Leaf(c) :: Nil) => Int32.fromString(Char.toString(c)) |> Option.getWithDefault(0)
        case CFGTree.Node('S', CFGTree.Leaf('(') :: subtree :: CFGTree.Leaf(')') :: Nil) => eval(subtree) 
        case CFGTree.Node('S', left :: CFGTree.Leaf(op) :: right :: Nil) => 
            let (l, r) = (eval(left), eval(right));
            match op {
                case '+' => l + r
                case '*' => l * r
                case _ => ???
            }
        case _ => println(tree);???
    };

    let cfg = Map#{
        'S' => Set#{ 
            CFGChar.Var('S') :: CFGChar.Alph('+') :: CFGChar.Var('S') :: Nil,
            CFGChar.Var('S') :: CFGChar.Alph('*') :: CFGChar.Var('S') :: Nil,
            CFGChar.Alph('(') :: CFGChar.Var('S') :: CFGChar.Alph(')') :: Nil,
            CFGChar.Alph('0') :: Nil,
            CFGChar.Alph('1') :: Nil,
            CFGChar.Alph('2') :: Nil,
            CFGChar.Alph('3') :: Nil,
            CFGChar.Alph('4') :: Nil,
            CFGChar.Alph('5') :: Nil,
            CFGChar.Alph('6') :: Nil,
            CFGChar.Alph('7') :: Nil,
            CFGChar.Alph('8') :: Nil,
            CFGChar.Alph('9') :: Nil
        }
    };

    let (cnf, varmap, alphmap) = deadGrammarToCNF(cfg);
    let cnftrees = cnf |> parseCNF(String.toList("(1+4+5)*2"));
    let trees = cnftrees |> Set.map(t -> convertCNFToCFGParseTree(t, varmap, alphmap) |> List.toSet) |> Set.flatten;

    assert(trees |> Set.forAll(t -> verifyCFGTree(t, cfg)));
    trees |> Set.forEach(t -> {
        println("${t}: ");
        let v = eval(t);
        println("- evaluated to: ${v}")
    });

    ()
}

def unitRecreationTest(): Unit \ IO = {
    let cfg: Grammar[Char, Char] = Map#{
        'S' => Set#{
            CFGChar.Var('S') :: CFGChar.Alph('+') :: CFGChar.Var('T') :: Nil, 
            CFGChar.Var('T') :: Nil
        },
        'T' => Set#{
            CFGChar.Var('T') :: CFGChar.Alph('*') :: CFGChar.Var('F') :: Nil, 
            CFGChar.Var('F') :: Nil
        },
        'F' => Set#{
            CFGChar.Alph('(') :: CFGChar.Var('S') :: CFGChar.Alph(')') :: Nil, 
            CFGChar.Alph('a') :: Nil
        }
    };


    let deadcfg = removeUnitProductions(cfg);
    let (cnf, varmap, alphmap) = deadGrammarToCNF(deadcfg);

    let cnftrees = cnf |> parseCNF(String.toList("a"));
    let trees1 = cnftrees |> Set.map(t -> convertCNFToCFGParseTree(t, varmap, alphmap) |> List.toSet) |> Set.flatten;
    let trees2 = trees1 |> Set.map(tree -> recreateUnitProductions(tree, cfg)) |> Set.flatten;
    
    trees2 |> Set.filter(t -> match t {
        case CFGTree.Node('S', _) => true
        case _ => true
    }) |> Set.forEach(println);
    ()
}
