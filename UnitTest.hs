module Main where
import Monad
import Test.HUnit
import System
import Dance hiding (main)

showB :: (Show a) => [(a, Int)] -> String
showB [] = ""
showB (x:xs) = (show x) ++ "  " ++ (showB xs)


pt_a = SPoint "a" (1,0)
pt_b = SPoint "b" (1,1)
move_a = Move ["a"] (1,1)
fig_ab = SFigure "ab" [pt_a, pt_b] [Link "a" "b"]

fig_ab_2 = SFigure "ab" [SPoint "a" (2,1), SPoint "b" (2,2)] [Link "a" "b"]
-- moves
n_m = []
move_x_1_1 = Move ["x"] (1,1)
move_ab_1_1 = Move ["ab"] (1,1)
defs = [SDefMove "ab" [Move ["ab"] (1,1) , Move ["ab"] (1,1)],
        SDefFig "ab" fig_ab]

moves = [move_x_1_1 , move_ab_1_1 ]

plst = [ TestCase $ assertEqual "<+>.1"  (2,2) $ (1,1)<+>(1,1),
         -- If given a point and nomove sequence then do not move.
         TestCase $ assertEqual "bigStep.Point.NoMove"
                (SPoint "x" (4,3), SFrame []) $ bigStep ([], SPoint "x" (4,3), n_m, SFrame []),
         TestCase $ assertEqual "bigStep.Point.Move"
                (SPoint "x" (5,4), SFrame []) $ bigStep ([], SPoint "x" (4,3), [move_x_1_1], SFrame []),
         TestCase $ assertEqual "bigStep.Figure.NoMove"
                (fig_ab, SFrame []) $ bigStep ([], fig_ab, [], SFrame []),
         TestCase $ assertEqual "bigStep.Figure.Move"
                 (fig_ab_2, SFrame []) $ bigStep ([], fig_ab, [move_ab_1_1] , SFrame []),
         -- Do not move if it is not addressed to the object.
         TestCase $ assertEqual "bigStep.Point.Move.X"
                (SPoint "y" (4,3), SFrame []) $ bigStep ([], SPoint "y" (4,3), [move_x_1_1] , SFrame []),
         TestCase $ assertEqual "bigStep.Figure.Move.X"
                (fig_ab, SFrame []) $ bigStep ([], fig_ab, [move_x_1_1] , SFrame []),

         TestCase $ assertEqual "bigStep.Figure.Move.Step"
                (SPoint "a" (2,1),SFrame [SPoint "a" (1,0),SPoint "a" (2,1)])
                (bigStep ([], pt_a, [Step , move_a , Step ], SFrame [])),

         TestCase $ assertEqual "bigStep.Figure.Move.Step.1"
                (fig_ab, SFrame [fig_ab])
                (bigStep ([], fig_ab, [Step] , SFrame [])), -- correct

         TestCase $ assertEqual "bigStep.Figure.Move.Step.2"
                (fig_ab_2, SFrame [fig_ab])
                (bigStep ([], fig_ab, [move_ab_1_1] , SFrame [fig_ab])), -- correct

         TestCase $ assertEqual "bigStep.Figure.Move.Step.3"
                (fig_ab_2, SFrame [fig_ab])
                (bigStep ([], fig_ab, [Step , move_ab_1_1 ], SFrame [])), -- correct

         TestCase $ assertEqual "bigStep.Figure.Move.Step.4"
            (SFigure "ab" [SPoint "a" (2,1),SPoint "b" (2,2)] [Link "a" "b"],SFrame [fig_ab_2])
            (bigStep ([], fig_ab, [move_ab_1_1 , Step ], SFrame [])),

         TestCase $ assertEqual "bigStep.Figure.Move.Step.5"
                 (fig_ab_2, SFrame [fig_ab, fig_ab_2])
                 (bigStep ([], fig_ab, [Step ,move_ab_1_1, Step] , SFrame [])),

         TestCase $ assertEqual "bigStep.Figure.Move.Step.6"
                (fig_ab_2, SFrame [fig_ab_2])
                (bigStep ([], fig_ab, [move_ab_1_1, Step], SFrame [])),

         TestCase $ assertEqual "bigStep.Figure.Move.Get"
            (SFigure "ab" [SPoint "a" (3,2),SPoint "b" (3,3)] [Link "a" "b"],SFrame [])
            (bigStep (defs, fig_ab, [GetMove "ab"], SFrame [])),

         TestCase $ assertEqual "bigStep.Figure.Move.Get"
            (SFigure "ab" [SPoint "a" (3,2),SPoint "b" (3,3)] [Link "a" "b"],SFrame [])
            (bigStep (defs, GetFigure "ab",[GetMove "ab"] , SFrame []))
       ]

showRes c@(Counts cases tried err fail) = "\n-> " ++ show c

unittest = runTestTT $ TestList $ plst

main = do c <- Main.unittest
          System.exitWith $ codeGet (errors c) (failures c)


codeGet errs fails
 | fails > 0       = ExitFailure 2
 | errs > 0        = ExitFailure 1
 | otherwise       = ExitSuccess

