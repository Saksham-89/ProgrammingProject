package ProgrammingProject.ai;

import ProgrammingProject.model.DotsAndBoxesGame;
import ProgrammingProject.model.DotsAndBoxesMove;
import ProgrammingProject.model.Line;
import ProgrammingProject.model.MoveResult;

public class SmartStrategy implements Strategy {
    @Override
    public String getName() {
        return "Smart Strategy";
    }

    @Override
    public DotsAndBoxesMove determineMove(DotsAndBoxesGame game) {
        int depth = 3;
        return miniMax(game, depth, true, Integer.MIN_VALUE, Integer.MAX_VALUE).move;
    }

    private MoveResult miniMax(DotsAndBoxesGame game, int depth, boolean isMaximizingPlayer, int alpha, int beta){
        if (depth == 0 || game.gameOver()){
            return new MoveResult(evaluateGame(game), null);
        }

        if (isMaximizingPlayer){
            MoveResult bestMove = new MoveResult(Integer.MIN_VALUE, null);
            for (DotsAndBoxesMove move : game.getValidMoves()) {
                DotsAndBoxesGame clonedGame = game.deepCopy();
                clonedGame.doMove(move);
                int moveValue = miniMax(clonedGame, depth - 1, false, alpha, beta).value;
                if (moveValue > bestMove.value) {
                    bestMove.value = moveValue;
                    bestMove.move = move;
                }
                alpha = Math.max(alpha, bestMove.value);
                if (beta <= alpha) {
                    break;
                }
            }
            return bestMove;
        } else {
            MoveResult bestMove = new MoveResult(Integer.MAX_VALUE, null);
            for (DotsAndBoxesMove move : game.getValidMoves()) {
                DotsAndBoxesGame clonedGame = game.deepCopy();
                clonedGame.doMove(move);
                int moveValue = miniMax(clonedGame, depth - 1, true, alpha, beta).value;
                if (moveValue < bestMove.value) {
                    bestMove.value = moveValue;
                    bestMove.move = move;
                }
                beta = Math.min(beta, bestMove.value);
                if (beta <= alpha) {
                    break;
                }
            }
            return bestMove;
        }
    }

    private int evaluateGame(DotsAndBoxesGame game) {
        return game.getBoard().getScore(Line.BLUE) - game.getBoard().getScore(Line.RED);
    }

}
