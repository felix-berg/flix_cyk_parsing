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

def unroll(list: List[Set[t]]): Set[List[t]] with Order[t] = match list {
  case x :: Nil => x |> Set.map(elm -> elm :: Nil)
  case x :: xs => unroll(xs) |> Set.map(ys -> x |> Set.map(y -> y :: ys)) |> Set.flatten
  case Nil => Set.empty()
  case _ => ???
}

def getDirectProducibleVars(var: v, cfg: Grammar[v, a]): Set[v] with Order[v], Order[a] = match Map.get(var, cfg) {
  case Option.None => Set#{}
  case Option.Some(prods) => prods |> Set.filterMap(prod -> match prod {
    case CFGChar.Var(war) :: Nil => Some(war)
    case _ => None
  }) 
}

def getChainsImpl(var: v, cfg: Grammar[v, a], ignore: Set[v]): Set[List[v]] with Order[v], Order[a] = 
  getDirectProducibleVars(var, cfg) 
    |> Set.filter(war -> not Set.memberOf(war, ignore))
    |> Set.map(war -> getChainsImpl(war, cfg, ignore |> Set.insert(war))) |> Set.flatten 
    |> Set.map(chain -> var :: chain) |> Set.insert(var :: Nil)

def getChains(var: v, cfg: Grammar[v, a]): Set[List[v]] with Order[v], Order[a] = 
  getChainsImpl(var, cfg, Set.empty())

def recreateUnitProductions(tree: CFGTree[v, a], cfg: Grammar[v, a]): Set[CFGTree[v, a]] with Order[v], Order[a] = match tree {
  case CFGTree.Leaf(_) => Set#{tree}
  case CFGTree.Node(var, children) =>
    let prod = children |> List.map(t -> getRoot(t));
    let subtrees = children 
      |> List.map(child -> recreateUnitProductions(child, cfg))
      |> unroll;
  
    // get chains where the last var A has A -> children
    let chains = getChains(var, cfg) |> Set.filter(chain -> match List.last(chain) {
      case Option.Some(war) => 
        Map.getWithDefault(war, Set.empty(), cfg) |> Set.memberOf(prod)
      case Option.None => false
    });

    Set.product(chains, subtrees) |> Set.map(match (chain, subtree) -> {
      chain |> List.foldRight((war, st) -> CFGTree.Node(war, st) :: Nil, subtree)
    }) |> Set.map(lst -> match lst {
      case x :: Nil => x
      case _ => ???
    })
} 
