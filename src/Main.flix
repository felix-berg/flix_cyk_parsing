def main(): Unit \ IO = {
    // dumbTest();
    // bracketsTest();
    // testBrackets();
    // convertParseTreeTest();
    // arithmeticTest();

    let cfg = Map#{
        'S' => Set#{
            CFGChar.Var('S') :: CFGChar.Alph('+') :: CFGChar.Var('T') :: Nil, CFGChar.Var('T') :: Nil
        },
        'T' => Set#{
            CFGChar.Var('T') :: CFGChar.Alph('*') :: CFGChar.Var('F') :: Nil, CFGChar.Var('F') :: Nil,
            CFGChar.Var('F') :: Nil
        },
        'F' => Set#{
            CFGChar.Alph('(') :: CFGChar.Var('S') :: CFGChar.Alph(')') :: Nil, 
            CFGChar.Var('a') :: Nil
        }
    };

    let { cfg = deadcfg, derivable = drv } = removeUnitProductions(cfg);
    let (cnf, varmap, alphmap) = deadGrammarToCNF(deadcfg);

    let cnftrees = cnf |> parseCNF(String.toList("a*a+a"));
    let trees1 = cnftrees |> Set.map(t -> convertCNFToCFGParseTree(t, varmap, alphmap) |> List.toSet) |> Set.flatten;
    // let trees2 = trees1 |> Set.map(t -> match t {
    //     case CFGTree.Node(var, lst) => match Map.get(var, drv) {
    //         case Option.Some(tops)
    //         case Option.None => ???
    //     } 
    //     case _ => t
    // }) |> Set.flatten;

    println("")
}