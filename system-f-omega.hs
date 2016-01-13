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