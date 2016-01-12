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

