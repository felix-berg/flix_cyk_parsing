enum Vars with Eq, Order, ToString {
    case BinOp,
    case BinOpExp,
    case Exp,
    case IfThenElse,
    case BoolLit
    case Digit
}

enum Token with Eq, Order, ToString {
    case True, case False,
    case Digitt(Char),
    case Op(Char),
    case If,
    case Else,
    case LBracket,
    case RBracket,
    case LParen,
    case RParen
}

mod Ast {

    use CFGChar.{Alph, Var}
    use Vars.{ BoolLit, Exp, BinOp, BinOpExp, IfThenElse, Digit }
    use Token.{ Digitt, Op, If, Else, LBracket, RBracket, LParen, RParen, True, False }
    use CFGTree.{Leaf, Node}

    pub enum Op with Eq, Order, ToString {
        case Plus, case Minus, case Mult, case Div
    }

    pub enum Expp with Eq, Order, ToString {
        case BinOpExp(Expp, Op, Expp),
        case IfThenElse(Expp, Expp, Expp),
        case IntLit(Int32),
        case BoolLit(Bool)
    }

    pub enum Val with Eq, Order, ToString {
        case IntVal(Int32), 
        case BoolVal(Bool)
    }

    pub def transform(tree: CFGTree[Vars, Token]): Expp \ IO = match tree { 
        case Node(Exp, children) => match children {
            case Leaf(LBracket) :: exp :: Leaf(RBracket) :: Nil => transform(exp)    

            case Node(BinOpExp, left :: Node(BinOp, Leaf(Op(op)) :: Nil) :: right :: Nil) :: Nil => 
                let o = match op {
                    case '+' => Op.Plus
                    case '-' => Op.Minus
                    case '*' => Op.Mult
                    case '/' => Op.Div
                    case _ => ???
                };
                Expp.BinOpExp(transform(left), o, transform(right))

            
            case Node(IfThenElse, 
                Leaf(If) :: Leaf(LBracket) :: cond :: Leaf(RBracket) 
                        :: then :: Leaf(Else) :: els :: Nil) :: Nil => 
                Expp.IfThenElse(transform(cond), transform(then), transform(els))
        
            case Node(Digit, Leaf(Digitt(char)) :: Nil) :: Nil => match Char.getNumericValue(char) {
                case Some(iv) => Expp.IntLit(iv)
                case None => ???
            }

            case Node(BoolLit, Leaf(b) :: Nil) :: Nil => match b {
                case True => Expp.BoolLit(true)
                case False => Expp.BoolLit(false)
                case _ => ???
            }

            case _ => println(tree); ???
        }
        case _ => ???
    } 

    pub def eval(exp: Expp): Val = match exp {
        case Expp.BinOpExp(left, op, right) => 
            let (l, r) = (eval(left), eval(right));
            match (l, op, r) {
                case (Val.IntVal(ll), Op.Plus,  Val.IntVal(rr))  => Val.IntVal(ll + rr)
                case (Val.IntVal(ll), Op.Minus, Val.IntVal(rr))  => Val.IntVal(ll - rr)
                case (Val.IntVal(ll), Op.Mult,  Val.IntVal(rr))  => Val.IntVal(ll * rr)
                case (Val.IntVal(ll), Op.Div,   Val.IntVal(rr))  => Val.IntVal(ll / rr)
                case _ => ???
            }
        case Expp.IfThenElse(cond, then, els) => 
            let b = eval(cond);
            match b {
                case Val.BoolVal(val) => if (val) {
                    eval(then)
                } else {
                    eval(els)
                }
                case _ => ???
            }
        case Expp.IntLit(i) => Val.IntVal(i)
        case Expp.BoolLit(b) => Val.BoolVal(b)
        case _ => ???
    }
}

def main(): Unit \ IO = {
    // dumbTest();
    // bracketsTest();
    // testBrackets();
    // convertParseTreeTest();
    // arithmeticTest();
    // unitRecreationTest();
    

    use CFGChar.{Alph, Var};
    use Vars.{ BoolLit, Exp, BinOp, BinOpExp, IfThenElse, Digit };
    use Token.{ Digitt, Op, If, Else, LBracket, RBracket, LParen, RParen, True, False };

    let cfg: Grammar[Vars, Token] = Map#{
        Digit     => Set#{ Alph(Digitt('0')) :: Nil,
                            Alph(Digitt('1')) :: Nil, 
                            Alph(Digitt('2')) :: Nil, 
                            Alph(Digitt('3')) :: Nil, 
                            Alph(Digitt('4')) :: Nil, 
                            Alph(Digitt('5')) :: Nil, 
                            Alph(Digitt('6')) :: Nil, 
                            Alph(Digitt('7')) :: Nil, 
                            Alph(Digitt('8')) :: Nil, 
                            Alph(Digitt('9')) :: Nil },

        BoolLit    => Set#{ Alph(True) :: Nil, Alph(False) :: Nil },
                
        BinOp      => Set#{ Alph(Op('+')) :: Nil,
                            Alph(Op('-')) :: Nil,
                            Alph(Op('*')) :: Nil,
                            Alph(Op('/')) :: Nil },
        
        BinOpExp   => Set#{ Var(Exp) :: Var(BinOp) :: Var(Exp) :: Nil},
        
        IfThenElse => Set#{ Alph(If) :: Alph(LBracket) :: Var(Exp) :: Alph(RBracket) :: Var(Exp) :: Alph(Else) :: Var(Exp) :: Nil },
        
        Exp => Set#{ Alph(LBracket) :: Var(Exp) :: Alph(RBracket) :: Nil,
                     Var(BinOpExp) :: Nil,
                     Var(IfThenElse) :: Nil,
                     Var(Digit) :: Nil,
                     Var(BoolLit) :: Nil }
    };

    // let tointlit = (str: String) -> str |> String.toList |> List.map(c -> Digitt(c));

    let test = If :: LBracket :: True :: RBracket 
            :: Digitt('1') 
        :: Else 
            :: Digitt('2') :: Op('+') :: Digitt('3')
        :: Nil;

    match createParser(cfg) {
        case Option.Some(parser) => 
            parser(test) 
            |> Set.filter(tree -> match tree {
                case CFGTree.Node(Exp, _) => true
                case _ => false
            })
            |> Set.forEach(tree -> {
                assert(verifyCFGTree(tree, cfg));
                let ast = Ast.transform(tree);
                println(Ast.eval(ast))
            })

        case Option.None => 
            println("Couldn't create parser")
    };

    println("")
}