enum CFGTree[v, a] with Order, Eq, ToString {
    case Node(v, List[CFGTree[v, a]]),
    case Leaf(a)
}

def convertParseTree(tree: CNFTree[Int32, a], map: Map[Int32, Set[CFGProd[v, a]]]): List[CFGTree[v, a]] with Order[v], Order[a] = match tree {
    case CNFTree.Leaf(iv, a) => match Map.get(iv, map) {
        case Option.Some(set) => ???
        case Option.None => ???
    }
    case CNFTree.Node(iv, x, y) => ???
}

def main(): Unit \ IO = {
    // dumbTest();
    // bracketsTest();
    // testBrackets();

    let cfg = Map#{
        'S' => Set#{ 
            CFGChar.Alph('c') :: Nil,
            CFGChar.Alph('a') :: CFGChar.Var('S') :: CFGChar.Alph('b') :: Nil
        }
    };

    let (cnf, map) = deadGrammarToCNF(cfg);
    cnf |> Map.forEach((var, prod) -> println("${var}: ${prod}"));
    // map |> Map.forEach((var, prod) -> println("r${var}: ${prod}"));

    let cnftrees = cnf |> parseCNF(String.toList("acb"));
    println("Before: ");
    cnftrees |> Set.forEach(println);
    cnftrees |> Set.map(tree -> convertParseTree(tree, map)) |> Set.forEach(println);
    ()
}