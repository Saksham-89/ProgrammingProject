package ProgrammingProject.ai;

import ProgrammingProject.model.DotsAndBoxesGame;
import ProgrammingProject.model.DotsAndBoxesMove;
import java.util.Random;

/**
 * A naive strategy for playing the Dots and Boxes game.
 * This strategy selects a valid move randomly without any sophisticated logic.
 */
public class NaiveStrategy implements Strategy {

    /**
     * Returns the name of this strategy.
     *
     * @return the name of the strategy
     */
    @Override
    public String getName() {
        return "Naive Strategy";
    }

    /**
     * Determines a move in the Dots and Boxes game based on a naive strategy.
     * It randomly selects one of the valid available moves.
     *
     * @param game the current state of the Dots and Boxes game
     * @return a randomly chosen valid move
     */
    //@ requires game != null && !game.getValidMoves().isEmpty();
    //@ ensures \result != null;
    @Override
    public DotsAndBoxesMove determineMove(DotsAndBoxesGame game) {
        Random random = new Random();
        int randomNumber = random.nextInt(game.getValidMoves().size());
        System.out.println(game.getValidMoves().get(randomNumber));
        return game.getValidMoves().get(randomNumber);
    }
}
