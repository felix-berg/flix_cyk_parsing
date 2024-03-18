enum CNFProd[v, a] with Order, Eq {
    case Terminal(a),
    case NonTerminal(v, v)
}

type alias CNFGrammar[v, a] = List[(v, Set[CNFProd[v, a]])]
def getVarsWith(prod: CNFProd[v, a], cnf: CNFGrammar[v, a]): Set[v] with Order[a], Order[v] =
    List.foldLeft((set, pair) -> {
        let (v, vprods) = pair;
        if (Set.memberOf(prod, vprods)) set |> Set.insert(v) 
        else set
    }, Set.empty(), cnf)

def rangeInc(f: Int32, t: Int32): List[Int32] = List.range(f, t + 1)

type alias CYKTable[v: Type, ef: Eff] = Int32 -> Int32 -> Set[(v, Int32)] \ ef

def getCYKTable(str: List[a], cnf: CNFGrammar[v, a], rg: Region[r]): Option[CYKTable[v, r]] \ r
    with Order[v], Order[a] = match str { case List.Nil => Option.None case List.Cons(_, _) => 
        let n: Int32 = List.length(str);
        let arr = Array.repeat(rg, n * n, Set.empty());

        let computeIdx = (i, j) -> i * n + j; 
        let get = (i, j) -> Array.get(computeIdx(i, j), arr);
        let add = (i, j, s: Set[(v, Int32)]) -> {
            let idx = computeIdx(i, j);
            let new = Set.union(s, get(i, j));
            Array.put(new, idx, arr)
        };

        str |> List.forEachWithIndex((idx, char) -> 
                getVarsWith(CNFProd.Terminal(char), cnf) |> 
                Set.map(var -> (var, idx)) |>
                add(idx, idx)
            );

        foreach (len <- rangeInc(2, n); i <- rangeInc(0, n - len)) {
            let j = i + len - 1;
            // left: [i, k], right: [k + 1, j]
            foreach (k <- rangeInc(i, j - 1)) {
                let (lvars, rvars) = (get(i, k), get(k + 1, j));
                foreach ((l, _) <- lvars; (r, _) <- rvars) {
                    getVarsWith(CNFProd.NonTerminal(l, r), cnf) |>
                    Set.map(var -> (var, k)) |>  
                    add(i, j)
                }
            }
        };
        
        Option.Some(get)
}

// return all variables in `cnf` from which `str` can be derived.
def derivableFromCNF(str: List[a], cnf: CNFGrammar[v, a]): Set[v] with Order[a], Order[v] = {
    region cyk {
        getCYKTable(str, cnf, cyk) |> Option.map(get -> {
            let vars: Set[(v, Int32)] = get(0, List.length(str) - 1);
            Set.foldLeft((vs, v) -> vs |> Set.insert(fst(v)), Set.empty(), vars)
        }) |> Option.getWithDefault(Set.empty())
    }
}

enum CNFTree[v, a] with Eq, Order, ToString {
    case Leaf(v, a),
    case Node(v, CNFTree[v, a], CNFTree[v, a])
}

mod Set {
    pub def product(s: Set[a], t: Set[b]): Set[(a, b)] with Order[a], Order[b] = 
        s |> Set.map(u -> t |> Set.map(v -> (u, v))) |> Set.flatten
}

// build the set of valid derivation trees of the substring  xi...xj of `str` based on the cyk table `table`
def buildCNFTree(i: Int32, j: Int32, str: List[a], table: CYKTable[v, r]): Set[CNFTree[v, a]] \ r
    with Order[a], Order[v] =
    if (i == j) {
        str |> List.slice(start = i, end = i + 1) |> List.head |> 
        Option.map(char ->  table(i, j) |> 
                            Set.map((pair) -> {
                                let (var, _) = pair; 
                                CNFTree.Leaf(var, char)
                            })
        ) |>
        Option.getWithDefault(Set.empty())
    } else {
        table(i, j) |> Set.map(pair -> {
            let (var, k) = pair;
            let (leftset, rightset) = (buildCNFTree(i, k, str, table), buildCNFTree(k + 1, j, str, table));
            
            Set.product(leftset, rightset) |> 
            Set.map(p2 -> { let (l, r) = p2; CNFTree.Node(var, l, r) })
        }) |> Set.flatten
    }

def parseCNF(str: List[a], cnf: CNFGrammar[v, a]): Set[CNFTree[v, a]] with Order[a], Order[v] = {
    region cyk {
        match getCYKTable(str, cnf, cyk) {
            case Option.None => Set.empty()
            case Option.Some(table) => buildCNFTree(0, List.length(str) - 1, str, table)
        }
    }
}

def assert(b: Bool): Unit \ IO = if (not b) println("Boolean assertion failed") else ()
def assertEq(x: a, y: a):  Unit \ IO with Eq[a], ToString[a] = 
    if (x != y) println("Assertion error:\n - Expected: ${x}\n - Actual: ${y}")
    else ()
def assertNeq(x: a, y: a):  Unit \ IO with Eq[a], ToString[a] = 
    if (x == y) println("Assertion error:\n - Expected: ${x}\n - Actual: ${y}")
    else ()

def dumbTest(): Unit \ IO = {
    let cnf = ('S', Set#{ 
            CNFProd.Terminal(0),
            CNFProd.NonTerminal('S', 'S')
        }) :: List.Nil;
        
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
        ('S', Set#{ CNFProd.NonTerminal('L', 'A'), CNFProd.NonTerminal('L', 'R'), CNFProd.NonTerminal('S', 'S')}) ::
        ('A', Set#{ CNFProd.NonTerminal('S', 'R') }) ::
        ('L', Set#{ CNFProd.Terminal('(') }) ::
        ('R', Set#{ CNFProd.Terminal(')') }) :: Nil;

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

def main(): Unit \ IO = {
    dumbTest();
    bracketsTest()
}