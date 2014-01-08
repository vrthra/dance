> module Dance where
> import Graphics.Gloss
> import Debug.Trace
> import qualified Control.Exception as E

-------------------------------------------------------------------------------
SYNTAX
===============================================================================
offset ::= (i,i)

TODO: Add non constraining (x,y)
type Address = (_|x, _|y)

> type Offset = (Integer,Integer)

-------------------------------------------------------------------------------

relations specify the connection between named points.
(for now)

relation ::= [s s]

> type Symbol = String
> data Relation = Link Symbol Symbol
>                 deriving (Show, Eq)

e.g 
    To show that there is a stick connecting a and b
    [a b]

-------------------------------------------------------------------------------

figure ::= symbol -> offset
         | symbol -> figure* relation*

> data SFigure = SPoint Symbol Offset
>              | SFigure Symbol [SFigure] [Relation]
>              | GetFigure Symbol
>                 deriving (Show, Eq)


A frame collects the positions of current figures. It gets updated only when
Step is executed.

> data SFrame = SFrame [SFigure]
>               deriving (Show, Eq)


examples

    a -> (1,1)

    line_a_b -> a -> (1,1), b -> (2,2) [a b]

    bend -> a -> (1,0), b -> (0,0), c -> (0,1) [a b] [b c]

    triangle -> (bend -> a -> (1,0), b -> (0,0), c -> (0,1) [a b] [b c]) [c a]


-------------------------------------------------------------------------------

move ::= stop
       | move: symbol by: offset move
       | moves: [move]

> data Move = Move [Symbol] Offset
>           | Moves [Move]
>           | GetMove Symbol
>           | Add [Symbol] SFigure
>           | Del [Symbol]
>                 deriving (Show, Eq)

> type MSeq = [Move]


examples
    a -> (1,1) move: a by: (1,1)  => a -> (2,2)
    a -> (1,1) move: b by: (1,1)  => a -> (1,1)

    (line_a_b -> a -> (1,1), b -> (2,2) [a b])
        move: line_a_b a by: (3,3) =>
            (line_a_b -> a -> (4,4), b -> (2,2) [a b])
    
    (line_a_b -> a -> (1,1), b -> (2,2) [a b])
        move: line_a_b a by: (3,3), move: line_a_b b by: (3,3) =>
            (line_a_b -> a -> (4,4), b -> (5,5) [a b])

-------------------------------------------------------------------------------
def ::= def name = fig
      | def name = move* 
defs ::= def*

> data SDef = SDefMove Symbol MSeq
>           |  SDefFig Symbol SFigure
>              deriving (Show, Eq)
> type SDefs = [SDef]

-------------------------------------------------------------------------------
SEMANTICS
===============================================================================
\subset-of is specified as s=

> (<+>) :: Offset -> Offset -> Offset
> (i,j) <+> (k,l) = (i+k , j+l)

> (<:>) :: SFigure -> SFrame -> SFrame
> f <:> (SFrame lst) = SFrame $ lst ++ [f]

> lkup::SDefs -> Symbol -> SDef
> lkup [] name = error $ "Unable to find: " ++ name
> lkup (d@(SDefFig s f):defs) name
>   | s == name = d
>   | True = lkup defs name
> lkup (d@(SDefMove s m):defs) name
>   | s == name = d
>   | otherwise = lkup defs name
>  
> (<^#>) :: SDefs -> Symbol -> SFigure
> defs <^#> sym = case lkup defs sym of
>   (SDefFig s f) -> f

> defs <^-> sym = case lkup defs sym of
>   (SDefMove s m) -> m

> sym :: (SDefs, SFigure) -> Symbol
> sym (defs, SPoint s o) = s
> sym (defs, SFigure s f r) = s
> sym (defs, GetFigure s ) = sym (defs, (defs <^#> s))


DEF:
Judgement:
    defs: def (def.eval)> defs  s= defs x def x defs

> defEval :: SDefs -> SDef -> SDefs

| defs: def (def.eval)> def U defs

> defEval defs def = (def:defs)

MOV:
Judgement:
    defs: move (mov.eval)> move s= defs x move x move

> movEval :: (SDefs,Move) -> Move

| defs: move: s off (mov.eval)> move: s off

> movEval (defs,Move s off) = Move s off

| defs: moves: [m1..mn] (mov.eval)> = moves: m1'..mn'
|           where m1 (mov.eval)> = m1'
|                 mn (mov.eval)> = mn'

> movEval (defs,Moves ms) = Moves $ map (\m -> movEval (defs,m)) ms

| defs: getmove: sym (mov.eval)> = m'
|           where defs = {sym = m'}

> movEval (defs, GetMove s) = Moves m'
>         where m' = defs <^-> s


> movEval (defs, Add s f) = Add s f
> movEval (defs, Del s) = Del s


FIG:
Judgement:
    defs: figure (fig.eval)> figure s= defs x figure x figure

> figEval::(SDefs,SFigure) -> SFigure

| defs: (symbol offset) (fig.eval)> (symbol offset)

> figEval (defs, SPoint s o) = SPoint s o

| defs: (symbol [f1..fn] rel) (fig.eval)> symbol f1'..fn' rel
|           where f1 (fig.eval)> = f1'
|                 fn (fig.eval)> = fn'

> figEval (defs,SFigure s fs rs) = SFigure s (map (\f -> figEval (defs,f)) fs) rs

| defs: getfig: sym (fig.eval)> = f'
|           where defs = {sym = f'}

> figEval (defs, GetFigure s) = f'
>        where f' = defs <^#> s

FIGMOV:
vector addition <+> 
(x,y) <+> (x',y') = (x+x', y+y')

Judgement:
    defs: figure,move (fig.move)> figure

| defs: (symbol p) (move: [] o) (fig.move)> (symbol p')
|           where p' = o <+> p

> figMov ::(SDefs, SFigure, Move) -> SFigure
> figMov (defs, SPoint s p, Move [] o) = SPoint s p'
>       where p' = o <+> p

| defs: (fig s f1..fn rel) (move: [] o) (fig.move)> fig s f1''..fn'' rel
|      where defs:f1 (fig.eval)> f1'   defs:f1' move: [] o (fig.move)> f1''
|            defs:fn (fig.eval)> fn'   defs:fn' move: [] o (fig.move)> fn''

> figMov (defs, SFigure s figs rels, Move [] o) = SFigure s figs'' rels
>       where figs' = map (\f -> figEval (defs, f) ) figs
>             figs'' = map (\f -> figMov (defs, f, Move [] o) ) figs'

| defs: (getfig s) (move: [] o) (fig.move)>  f'
|                                         where (getfig s) (fig.eval)> f
|                                               f move: [] o (fig.move)> f'


> figMov (defs, GetFigure s, Move [] o) = f'
>       where f = figEval (defs,GetFigure s)
>             f' = figMov (defs, f, Move [] o)

| defs: (sym [f1..fi..fn] rels) (move: [s1..sn] o) (fig.move)> (sym [f1..fi''..fn] rels)
|      where  sym fi = s1
|             fi (fig.eval)> fi'
|             fi', move [s2..sn] (fig.move)> fi''

> figMov (defs, SFigure s_ fs rel, Move (m:ms) o) = SFigure s_ fs' rel
>       where fs' = map (\f -> case (sym (defs,f)) == m of
>                                   True -> figMov (defs, fe f,Move ms o)
>                                   False -> f
>                      ) fs
>             fe f = figEval (defs,f)


> figMov (defs, fig, Moves []) = fig
> figMov (defs, fig, Moves (m:ms)) = f''
>       where f' = figMov (defs, fig, m)
>             f'' = figMov (defs, f', Moves ms)


| defs: (getfig: sym ) m (fig.move)> f''
|       where (getfig: sym) (fig.eval)> f'
|             f',m (fig.move)> f''

> figMov (defs, GetFigure s, m) = f''
>       where f' = figEval (defs, GetFigure s)
>             f'' = figMov (defs, f',m)

| defs: f (getmove: s) (fig.move)> f''
|       where (getmove: sym) (mov.eval)> m'
|             f (fig.eval)> f'
|             f',m' (fig.move)> f''

> figMov (defs, f, GetMove s) = f''
>       where f' = figEval (defs, f)
>             m' = movEval (defs, GetMove s)
>             f'' = figMov (defs, f', m')

| defs: (sym figs rels) (add: [] fig) (fig.move)> (sym fig:figs rels)

> figMov (defs, SFigure s_ figs rels, Add [] fig) = SFigure s_ (fig:figs) rels

| defs: (sym [f1..fi..fn] rels) (add: [s1..sn] fig) (fig.move)> (sym [f1..fi''..fn] rels)
|       where sym fi = s1
|             fi (fig.eval)> fi'
|             fi' add: [s2..sn] (fig.move)> fi''

> figMov (defs, SFigure s_ fs rel, Add (m:ms) fig) = SFigure s_ fs' rel
>       where fs' = map (\f -> case (sym (defs,f)) == m of
>                                   True -> figMov (defs, fe f,Add ms fig)
>                                   False -> f
>                      ) fs
>             fe f = figEval (defs,f)


| defs: fig (del: []) (fig.move)> fig

> figMov (defs, f, Del [] ) = f

| defs: (sym [f1..fi..fn] rels) (del: [s1]) (fig.move)> (sym [f1..fi-1,fi+1..fn] rels)
|       where sym fi = s1

> figMov (defs, SFigure s_ fs rel, Del [m]) = SFigure s_ fs' rel
>       where fs' = filter (\f -> sym (defs,f) /= m) fs


| defs: (sym [f1..fi..fn] rels) (del: [s1..sn]) (fig.move)> (sym [f1..fi''..fn] rels)
|       where sym fi = s1
|             fi (fig.eval)> fi'
|             fi' del: [s2..sn] (fig.move)> fi''

> figMov (defs, SFigure s_ fs rel, Del (m:ms)) = SFigure s_ fs' rel
>       where fs' = map (\f -> case (sym (defs,f)) == m of
>                                   True -> figMov (defs, fe f,Del ms)
>                                   False -> f
>                      ) fs
>             fe f = figEval (defs,f)


> figMov (defs,a,m) = error $ "Error: FigMov " ++ (show a) ++ ":>" ++ (show m)

ANIM:
Judgement:
    defs: frame,move (frame.eval)> frame

> frameEval::(SDefs,SFrame, MSeq) -> SFrame

| defs, frame: [f1..fp], [] (frame.eval)> frame: [f1..fp+q]

> frameEval (defs, frame, []) = frame

| defs, frame: [], m (frame.eval)> frame: []

> frameEval (defs, SFrame [], (m:ms)) = SFrame []

| defs, frame: [f1..fp], [m1..mq] (frame.eval)>  frame [f1..fp+q]
|   where defs:fp (fig.eval)> fp'
|         defs:m1 (mov.eval)> m1'
|         defs:fp',m1' (fig.move)> fp+1
|         defs: frame: f1..fp+1 [m2..mq] (frame.eval)> frame [f1..fp+q]

> frameEval (defs, SFrame fr@(f:fs), (m:ms)) = fr'
>       where f' = figEval (defs,f)
>             m' = movEval (defs,m)
>             f_nxt = figMov (defs,f',m')
>             fr' = frameEval (defs, SFrame (f_nxt:fr),ms)


-------------------------------------------------------------------------------
TYPES:

tc (defs, frame, move)

-------------------------------------------------------------------------------
IMPLEMENTATION

Limitations:
    We do not address the links by path. Instead we just name the points.
    This will lead to problems when two points similarly named need to be
    linked together. Like the end points of two arms.

> itof :: Integer -> Float
> itof n = fromInteger (toInteger n)

> lookupSyms::[SFigure]->Symbol->Maybe Offset
> lookupSyms [] sym = Nothing
> lookupSyms (f:fs) sym = case lookupSym f sym of
>                           Nothing -> lookupSyms fs sym
>                           Just x -> Just x

> lookupSym::SFigure->Symbol->Maybe Offset
> lookupSym (SPoint sym1 o1) sym2
>       | sym1 == sym2 = Just o1
>       | otherwise = Nothing
> lookupSym (SFigure sym fs rel) s = lookupSyms fs s

> convertRel::SFigure->[Picture]
> convertRel (SFigure sym fs rels) = map (\(Link a b) -> line [x a, x b] ) rels
>                       where x a = case (lookupSyms fs a) of
>                                               Just (x,y) -> (itof x, itof y)
>                                               Nothing -> error "Nothing found"




> draw :: SFigure -> Picture
> draw (SPoint sym (x,y)) = blank
> draw f@(SFigure sym figs rels) = Pictures $ (map (\fig -> draw fig ) figs) ++ (convertRel f)

> mydefs = [SDefMove "ab" [Move ["a"] (1,1)]]


> fig_triangle = SFigure "tri" [SPoint "x" (0,10), SPoint "y" (1,9), SPoint "z" (1,10)] [Link "x" "y", Link "y" "z", Link "x" "z"]
> fig_sq = SFigure "sq" [SPoint "x" (2,10), SPoint "y" (3,9), SPoint "z" (3,10), SPoint "t" (2,9)] [Link "x" "z", Link "x" "t", Link "y" "t", Link "z" "y"]


> fig_leg1 = SFigure "leg.left" [SPoint "a" (0,0), SPoint "b" (1,1)] [Link "a" "b"]
> fig_leg2 = SFigure "leg.right" [SPoint "b" (1,1), SPoint "a" (2,0)]  [Link "a" "b"]
> fig_legs = SFigure "legs" [fig_leg1, fig_leg2] []

> fig_arm1 = SFigure "arm.left" [SPoint "d" (0,2), SPoint "e" (1,2)] [Link "d" "e"]
> fig_arm2 = SFigure "arm.right" [SPoint "e" (1,2), SPoint "d" (2,2)]  [Link "d" "e"]
> fig_arms = SFigure "arms" [fig_arm1, fig_arm2] []

> fig_body = SFigure "body" [SPoint "g" (1,3), SPoint "e" (1,2), SPoint "b" (1,1)]  [Link "g" "e", Link "e" "b"]

> fig_man = SFigure "man" [fig_body, fig_arms, fig_legs] []

> myfig = SFigure "ab" [SPoint "a" (1,1), SPoint "b" (2,2), SPoint "c" (0,0)]  [Link "a" "b", Link "b" "c"]

> myseq = [GetMove "ab", GetMove "ab" , Move ["ab","a"] (1,0),  GetMove "ab" ,Move ["ab","b"] (0,1)]

> dance :: MSeq
> dance1 = [Moves [Move ["arm.left"] (0,-1)]]

> dance = [Moves [Move ["man","arms", "arm.left", "d"] (0,1), Move ["man", "arms", "arm.right", "d"] (0,1)],
>          Moves [Move ["man", "arms", "arm.left", "d"] (0,-1), Move ["man", "arms", "arm.right", "d"] (0,-1)],
>          Move ["man", "arms", "arm.left", "d"] (0,-1),
>          Add []  fig_triangle,
>          Move ["tri"] (0,-1),
>          Del ["tri"],
>          Add []  fig_sq,
>          Move ["sq"] (0,1),
>          Del ["sq"],
>          Moves [Move ["man", "legs", "leg.left", "a"] (1,0),Move ["man", "legs", "leg.right", "a"] (0,1)],
>          Move ["man"] (1,0)]


> mymove = Move ["ab"] (1,1)

> preresult = (mydefs, SFrame [SFigure "main" [fig_man] []], dance)

> result = frameEval preresult

> toPicture:: SFigure -> Picture
> toPicture f = Pictures $ [draw f]

> getFigure::SFrame->Int->SFigure
> getFigure (SFrame f) i = f!!i

> main::IO ()
> main = animateInWindow "Sticks" (450,150) (10,10) white frame
> frame time = do Scale 20 20 $ toPicture $ (getFigure result index)
>             where index = ((truncate time) `mod` 11)

