package ProgrammingProject.ai;

import ProgrammingProject.model.DotsAndBoxesGame;
import ProgrammingProject.model.DotsAndBoxesMove;
import ProgrammingProject.model.Line;
import ProgrammingProject.model.MoveResult;

/**
 * A smart strategy for playing the Dots and Boxes game, using the MiniMax algorithm.
 * This strategy evaluates the possible future states of the game to make an informed decision.
 */
public class SmartStrategy implements Strategy {

    /**
     * Returns the name of this strategy.
     *
     * @return the name of the strategy, "Smart Strategy".
     */
    @Override
    public String getName() {
        return "Smart Strategy";
    }

    /**
     * Determines the next move in the Dots and Boxes game using the MiniMax algorithm.
     * This method initiates a depth-limited search for the best move.
     *
     * @param game the current state of the Dots and Boxes game
     * @return the move determined to be the best according to the MiniMax algorithm
     */
    //@ requires game != null;
    //@ ensures \result != null;
    @Override
    public DotsAndBoxesMove determineMove(DotsAndBoxesGame game) {
        int depth = 3; // Depth limit for the MiniMax search
        return miniMax(game, depth, true, Integer.MIN_VALUE, Integer.MAX_VALUE).move;
    }

    /**
     * The MiniMax algorithm implementation for determining the best move.
     * It recursively evaluates all possible moves to a certain depth and chooses the optimal move.
     *
     * @param game the game state to evaluate
     * @param depth the current depth of the recursion
     * @param isMaximizingPlayer a flag indicating if the current player is maximizing or minimizing the score
     * @param alpha the current alpha value for alpha-beta pruning
     * @param beta the current beta value for alpha-beta pruning
     * @return a MoveResult object containing the value of the best move and the move itself
     */
    //@ requires game != null && depth >= 0;
    //@ ensures \result != null;
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

    /**
     * Evaluates the current state of the game.
     * This simple evaluation function calculates the score difference between the two players.
     *
     * @param game the current game state to evaluate
     * @return the score difference from the perspective of the blue player
     */
    //@ requires game != null;
    private int evaluateGame(DotsAndBoxesGame game) {
        // Score difference: Blue - Red
        return game.getBoard().getScore(Line.BLUE) - game.getBoard().getScore(Line.RED);
    }
}
