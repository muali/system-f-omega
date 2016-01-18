import Data.List

infixr ::->

data Kind = K
          | Kind ::-> Kind
          deriving (Show, Eq)

type TypeVar = String

infixr :->
infixl ::@

data Type = TVar TypeVar
          | Type :-> Type
          | TTAbs  (TypeVar, Kind) Type
          | Forall (TypeVar, Kind) Type
          | Exists (TypeVar, Kind) Type
          | Type ::@ Type
          deriving (Show)

type ExprVar = String

infixl :@
infixl :*

data Expr = EVar ExprVar
          | Abs (ExprVar, Type) Expr
          | TAbs (TypeVar, Kind) Expr
          | Expr :@ Expr
          | Expr :* Type
          | Pack (Type, Expr) Type
          | UnPack (TypeVar, ExprVar) Expr Expr
          deriving (Show)

data ContextItem = TypeA TypeVar Kind
                 | ExprA ExprVar Type

type Context = [ContextItem]


kindFromCtx :: Context -> TypeVar -> Maybe Kind
kindFromCtx ctx x = 
    let helper (TypeA v kind) = v == x 
        helper (ExprA _ _)    = False  in
    let item = find helper ctx in
        case item of Just (TypeA _ kind) -> Just kind
                     Nothing             -> Nothing

extendKindError :: String -> Type -> Either Kind String
extendKindError err t = Right $ err ++ "\n\t in " ++ (show t)

kindify :: Type -> Context -> Either Kind String

kindify (TVar x) ctx = let kind = kindFromCtx ctx x in 
                       case kind of Just res -> Left  res
                                    Nothing  -> Right $ "Type variable " ++ x ++ " not in context"

kindify te@(TTAbs (x, k) t) ctx = let tKind = kindify t $ ctx ++ [TypeA x k] in
                                  case tKind of Left tKindRes -> Left $ k ::-> tKindRes
                                                Right err     -> extendKindError err te

kindify te@(t1 ::@ t2) ctx = let tKind1 = kindify t1 ctx
                                 tKind2 = kindify t2 ctx in
                             case (tKind1, tKind2) of (Left (k1 ::-> k2), Left k3) | k1 == k3 -> Left k2
                                                      (Right err, _) -> extendKindError err te
                                                      (_, Right err) -> extendKindError err te
                                                      (_, _)         -> Right $ "Type application kind mismatch in " ++ (show te)

kindify te@(t1 :-> t2) ctx = let tKind1 = kindify t1 ctx
                                 tKind2 = kindify t2 ctx in
                             case (tKind1, tKind2) of (Left K, Left K) -> Left K
                                                      (Right err, _)   -> extendKindError err te
                                                      (_, Right err)   -> extendKindError err te
                                                      (_, _)           -> Right $ "Arror type kind mismatch in " ++ (show te)

kindify te@(Forall (tv, k) t) ctx = let kind = kindify t (ctx ++ [TypeA tv k]) in
                                        case kind of (Left K) -> Left K
                                                     (Left _) -> Right $ "Forall kind mismatch in " ++ (show te)
                                                     (Right err) -> extendKindError err te

kindify te@(Exists (tv, k) t) ctx = let kind = kindify t (ctx ++ [TypeA tv k]) in
                                        case kind of (Left K) -> Left K
                                                     (Left _) -> Right $ "Exists kind mismatch in " ++ (show te)
                                                     (Right err) -> extendKindError err te



findFreeName :: [(TypeVar, TypeVar)] -> [(TypeVar, TypeVar)] -> Type -> Type -> TypeVar
findFreeName ctx1 ctx2 type1 type2 = helper "X" where
    helper name | isFreeCtx ctx1 name && isFreeCtx ctx2 name && isFreeType type1 name && isFreeType type2 name = name
                | otherwise = helper $ name ++ "X"
    
    isFreeCtx ctx name = let found = find (\(v1, v2) -> v1 == name || v2 == name) ctx in
                         case found of Just _  -> False
                                       Nothing -> True

    isFreeType t name = case t of TVar v            -> v /= name
                                  t1 :-> t2         -> isFreeType t1 name && isFreeType t2 name
                                  TTAbs  (v1, _) t1 -> v1 /= name && isFreeType t1 name
                                  Forall (v1, _) t1 -> v1 /= name && isFreeType t1 name
                                  Exists (v1, _) t1 -> v1 /= name && isFreeType t1 name
                                  t1 ::@ t2         -> isFreeType t1 name && isFreeType t2 name

substTypeVar :: [(TypeVar, TypeVar)] -> TypeVar -> TypeVar
substTypeVar [] v = v
substTypeVar ((v1, v2):xs) v3 | v1 == v3  = v2
                              | otherwise = substTypeVar xs v3

substTypeAbs :: TypeVar -> Type -> Type -> Type
substTypeAbs v1 t1@(TVar v2) t2 | v1 == v2  = t2
                                | otherwise = t1

substTypeAbs v1 (t1' :-> t2') t2 = (substTypeAbs v1 t1' t2) :-> (substTypeAbs v1 t2' t2)

substTypeAbs v1 t1@(TTAbs (v2, k) t1') t2 | v1 == v2  = t1
                                          | otherwise = TTAbs (v2, k) (substTypeAbs v1 t1' t2)

substTypeAbs v1 t1@(Forall (v2, k) t1') t2 | v1 == v2  = t1
                                           | otherwise = Forall (v2, k) (substTypeAbs v1 t1' t2)

substTypeAbs v1 t1@(Exists (v2, k) t1') t2 | v1 == v2 = t1
                                           | otherwise = Exists (v2, k) (substTypeAbs v1 t1' t2)

substTypeAbs v1 (t1' ::@ t2') t2 = (substTypeAbs v1 t1' t2) ::@ (substTypeAbs v1 t2' t2)


instance Eq Type where
    (==) = helper [] [] where

        helper ctx1 ctx2 (TVar v1) (TVar v2) = let v1' = substTypeVar ctx1 v1
                                                   v2' = substTypeVar ctx2 v2 in
                                                v1 == v2
        
        helper ctx1 ctx2 (t1 :-> t2) (t3 :-> t4) = helper ctx1 ctx2 t1 t3 && helper ctx1 ctx2 t2 t4
        
        helper ctx1 ctx2 (TTAbs (v1, k1) t1) (TTAbs (v2, k2) t2) | k1 /= k2 = False
                                                                 | v1 == v2 = helper ctx1 ctx2 t1 t2
                                                                 | otherwise = helper ([(v1, findFreeName ctx1 ctx2 t1 t2)] ++ ctx1)
                                                                                      ([(v2, findFreeName ctx1 ctx2 t1 t2)] ++ ctx2)
                                                                                      t1 t2
        
        helper ctx1 ctx2 (Forall (v1, k1) t1) (Forall (v2, k2) t2) | k1 /= k2 = False
                                                                   | v1 == v2 = helper ctx1 ctx2 t1 t2
                                                                   | otherwise = helper ([(v1, findFreeName ctx1 ctx2 t1 t2)] ++ ctx1)
                                                                                        ([(v2, findFreeName ctx1 ctx2 t1 t2)] ++ ctx2)
                                                                                        t1 t2                                       

        helper ctx1 ctx2 (Exists (v1, k1) t1) (Exists (v2, k2) t2) | k1 /= k2 = False
                                                                   | v1 == v2 = helper ctx1 ctx2 t1 t2
                                                                   | otherwise = helper ([(v1, findFreeName ctx1 ctx2 t1 t2)] ++ ctx1)
                                                                                        ([(v2, findFreeName ctx1 ctx2 t1 t2)] ++ ctx2)
                                                                                        t1 t2

        helper ctx1 ctx2 (t1 ::@ t2) (t3 ::@ t4) = helper ctx1 ctx2 t1 t3 && helper ctx1 ctx2 t2 t4

        helper ctx1 ctx2 (TTAbs (v, K) t1 ::@ t2) t3 = helper ctx1 ctx2 (substTypeAbs v t1 t2) t3
        helper ctx1 ctx2 t1 (TTAbs (v, K) t2 ::@ t3) = helper ctx1 ctx2 t1 (substTypeAbs v t2 t3)
        helper _ _ _ _ = False


typeFromCtx :: Context -> ExprVar -> Maybe Type
typeFromCtx ctx x =
    let helper (TypeA _ _) = False
        helper (ExprA v t) = v == x in
    let item = find helper ctx in
        case item of Just (ExprA _ t) -> Just t
                     Nothing          -> Nothing

extendErrorType :: String -> Expr -> Either Type String
extendErrorType err e = Right $ err ++ "\n\t in" ++ (show e)

typeCheck :: Expr -> Context -> Either Type String
typeCheck (EVar v) ctx = let t = typeFromCtx ctx v in
                             case t of Just t' -> Left t'
                                       Nothing -> Right $ "Unknown variable: " ++ v

typeCheck e@(Abs (v, t) e1) ctx = let k = kindify t ctx 
                                      t' = typeCheck e1 $ ctx ++ [ExprA v t] in
                                    case (k, t') of (Right err, _) -> extendErrorType err e
                                                    (_, Right err) -> extendErrorType err e
                                                    (Left K, Left t'') -> Left $ t :-> t''
                                                    (Left _, _) -> Right $ "Invalid abstraction: " ++ (show e)

typeCheck e@(e1 :@ e2) ctx = let t1 = typeCheck e1 ctx
                                 t2 = typeCheck e2 ctx in
                              case (t1, t2) of (Left (t1' :-> t2'), Left t3') -> if t1' == t3' then Left t2'
                                                                              else Right $ "Invalid application: " ++ (show e)
                                               (Left _, Left _)               -> Right $ "Invalid application: " ++ (show e)
                                               (Right err, _)                 -> extendErrorType err e
                                               (_, Right err)                 -> extendErrorType err e

typeCheck e@(TAbs (tv, k) e1) ctx = let t = typeCheck e1 $ ctx ++ [TypeA tv k] in
                                        case t of Left t' -> Left $ Forall (tv, k) t'
                                                  Right err -> extendErrorType err e



typeCheck e@(e1 :* t1) ctx =  let t = typeCheck e1 ctx 
                                  k = kindify t1 ctx in
                                case (t, k) of (Left (Forall (tv, k1) t2), Left k2) -> if k1 == k2 then Left $ substTypeAbs tv t2 t1
                                                                                       else Right $ "Invalid type application: " ++ (show e)
                                               (Left _, Left _)                     -> Right $ "Invalid type application: " ++ (show e)
                                               (Right err, _)                       -> extendErrorType err e
                                               (_, Right err)                       -> extendErrorType err e

typeCheck e@(Pack (t1, e1) t@(Exists (tv2, k) t2)) ctx = let t1' = typeCheck e1 ctx
                                                             t2' = substTypeAbs tv2 t2 t1
                                                             k'  = kindify t ctx in
                                                         case (t1', t2', k') of (Left t1'', t2'', Left K) -> if t1'' == t2'' then Left t
                                                                                                              else Right $ "Invalid pack: " ++ (show e)
                                                                                (Left _, _, Left _) -> Right $ "Invalid pack: " ++ (show e)
                                                                                (Right err, _, _) -> extendErrorType err e
                                                                                (_, _, Right err) -> extendErrorType err e

typeCheck e@(Pack _ _) _ = Right $ "Invalid pack: " ++ (show e)

typeCheck e@(UnPack (tv, ev) e1 e2) ctx = let t1 = typeCheck e1 ctx in
                                            case t1 of (Left (Exists (tv', k) t1')) -> typeCheck e2 $ ctx ++ [TypeA tv k, ExprA ev t1']
                                                       (Left _) -> Right $ "Invalid unpack: " ++ (show e)
                                                       (Right err) -> extendErrorType err e


auto = TTAbs ("X", K) (TVar "X" :-> TVar "X")
a = TVar "A"
s1 = (Abs ("x", auto ::@ a) (EVar "x"))

pair = TAbs ("X", K) 
        (TAbs ("Y", K) 
          (Abs ("x", TVar "X") 
            (Abs ("y", TVar "Y") 
              (TAbs ("R", K) 
                (Abs ("p", TVar "X" :-> TVar "Y" :-> TVar "R") (EVar "p" :@ EVar "x" :@ EVar "y")
                  )))))

fst' = TAbs ("X", K)
        (TAbs ("Y", K)
          (Abs ("p", Forall ("R", K) ((TVar "X" :-> TVar "Y" :-> TVar "R") :-> TVar "R"))
            (((EVar "p") :* (TVar "X")) :@ (Abs ("x", TVar "X") (Abs ("y", TVar "Y") (EVar "x"))))))


ctxWithNatBool = [TypeA "Nat" K, TypeA "Bool" K, ExprA "5" (TVar "Nat"), ExprA "true" (TVar "Bool")]

s2 = fst' :* (TVar "Nat") :* (TVar "Bool") :@ (pair :* (TVar "Nat") :* (TVar "Bool") :@ (EVar "5") :@ (EVar "true"))