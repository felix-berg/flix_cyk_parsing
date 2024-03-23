enum CFGTree[v, a] with Order, Eq, ToString {
    case Node(v, List[CFGTree[v, a]]),
    case Leaf(a)
}

def convertParseTree(tree: CNFTree[Int32, a], varmap: Map[Int32, v], alphmap: Map[Int32, a]): List[CFGTree[v, a]] with Order[v], Order[a] = match tree {
    case CNFTree.Leaf(iv, a) => match Map.get(iv, alphmap) {
        case Option.Some(alphvar) => CFGTree.Leaf(a) :: Nil
        case Option.None => match Map.get(iv, varmap) {
            case Option.Some(var) => CFGTree.Node(var, CFGTree.Leaf(a) :: Nil) :: Nil
            case Option.None => ???
        }
    }
    // iv -> XY
    case CNFTree.Node(iv, x, y) => match Map.get(iv, varmap) {
        case Option.Some(var) => 
            let (l, r) = (convertParseTree(x, varmap, alphmap), convertParseTree(y, varmap, alphmap)); 
            let children = List.append(l, r);
            CFGTree.Node(var, children) :: Nil
        case Option.None => match Map.get(iv, alphmap) {
            case Option.Some(_) => ??? // iv -> XY where iv is a terminal production doesn't make any sense
            case Option.None => 
                let (l, r) = (convertParseTree(x, varmap, alphmap), convertParseTree(y, varmap, alphmap));
                List.append(l, r)
        }
    }
}

def main(): Unit \ IO = {
    // dumbTest();
    // bracketsTest();
    // testBrackets();

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
    cnftrees |> Set.map(tree -> convertParseTree(tree, varmap, alphmap)) 
        |> Set.forEach(println);
    ()
}