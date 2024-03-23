enum CFGTree[v, a] with Order, Eq, ToString {
    case Node(v, List[CFGTree[v, a]]),
    case Leaf(a)
}

def convertCNFToCFGParseTree(tree: CNFTree[Int32, a], varmap: Map[Int32, v], alphmap: Map[Int32, a]): List[CFGTree[v, a]] with Order[v], Order[a] = match tree {
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
            let (l, r) = (convertCNFToCFGParseTree(x, varmap, alphmap), convertCNFToCFGParseTree(y, varmap, alphmap)); 
            let children = List.append(l, r);
            CFGTree.Node(var, children) :: Nil
        case Option.None => match Map.get(iv, alphmap) {
            case Option.Some(_) => ??? // iv -> XY where iv is a terminal production doesn't make any sense
            case Option.None => 
                let (l, r) = (convertCNFToCFGParseTree(x, varmap, alphmap), convertCNFToCFGParseTree(y, varmap, alphmap));
                List.append(l, r)
        }
    }
}

def getRoot(tree: CFGTree[v, a]): CFGChar[v, a] = match tree {
    case CFGTree.Node(var, _) => CFGChar.Var(var)
    case CFGTree.Leaf(alph) => CFGChar.Alph(alph)
}

def verifyCFGTree(tree: CFGTree[v, a], cfg: Grammar[v, a]): Bool with Order[a], Order[v] = match tree {
    case CFGTree.Leaf(a) => getTerminals(cfg) |> Set.memberOf(a)
    case CFGTree.Node(var, lst) => 
        let prod = lst |> List.map(t -> getRoot(t));
        let isMember = match cfg |> Map.get(var) {
            case Option.Some(set) => Set.memberOf(prod, set)
            case Option.None => ???
        };

        isMember and (lst |> List.forAll(t -> verifyCFGTree(t, cfg)))
    case _ => ???
}
