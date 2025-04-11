type alias Parser[v, a] = List[a] -> Set[CFGTree[v, a]]
def createParser(cfg: Grammar[v, a]): Option[Parser[v, a]] with Order[v], Order[a] = 
    Option.point(()) |> Option.filter(_ -> {
        // can't have lambda productions
        let lambdaprods = cfg |> Map.exists((_, prods) -> prods |> Set.exists(prod -> isLambdaProduction(prod)));
        not lambdaprods
    }) 
    // TODO: check for unit-loops
    |> Option.map(_ -> {
        let deadcfg = removeUnitProductions(cfg);
        let (cnf, varmap, alphmap) = deadGrammarToCNF(deadcfg);

        (list: List[a]) -> {
            cnf |> parseCNF(list)
                |> Set.map(tree -> convertCNFToCFGParseTree(tree, varmap, alphmap))
                |> Set.filterMap(tree -> match tree {
                    case x :: Nil => Some(x)
                    case _ => None
                })
                |> Set.map(tree -> recreateUnitProductions(tree, cfg)) |> Set.flatten
        }
    })