package ProgrammingProject.ai;

import ProgrammingProject.model.DotsAndBoxesGame;
import ProgrammingProject.model.DotsAndBoxesMove;

/**
 * Defines the interface for strategies used in the Dots and Boxes game.
 * Implementing classes will provide specific strategies for making moves within the game.
 */
public interface Strategy {

    /**
     * Returns the name of the strategy.
     *
     * @return A string representing the name of the strategy.
     */
    String getName();

    /**
     * Determines the next move to make in a given Dots and Boxes game.
     * Implementing classes should provide logic to decide the best move based on the current game state.
     *
     * @param game The current state of the Dots and Boxes game.
     * @return The move that the strategy decides to make.
     */
    DotsAndBoxesMove determineMove(DotsAndBoxesGame game);
}
