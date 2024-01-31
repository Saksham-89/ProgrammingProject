package ProgrammingProject.ai;

import ProgrammingProject.model.*;

/**
 * Represents a computer player in the Dots and Boxes game.
 * This player uses a specified strategy to determine its moves.
 */
public class ComputerPlayer extends AbstractPlayer {

    private Line line;
    private ProgrammingProject.ai.Strategy strategy;

    /**
     * Constructs a new ComputerPlayer with a specific line and strategy.
     *
     * @param line the line associated with this player
     * @param strategy the strategy used by this player to make moves
     */
    //@ requires line != null && strategy != null;
    //@ ensures getLine() == line && getStrategy() == strategy;
    public ComputerPlayer(Line line, ProgrammingProject.ai.Strategy strategy){
        super(strategy.getName());
        this.line = line;
        this.strategy = strategy;
    }

    /**
     * Determines the next move for this player based on its strategy.
     *
     * @param game the current state of the Dots and Boxes game
     * @return the move determined by the player's strategy
     */
    //@ requires game != null;
    //@ ensures \result != null;
    public DotsAndBoxesMove determineMove(DotsAndBoxesGame game){
        return strategy.determineMove(game);
    }

    /**
     * Returns the strategy used by this computer player.
     *
     * @return the strategy
     */
    //@ ensures \result != null;
    public Strategy getStrategy(){
        return strategy;
    }

    /**
     * Returns the line associated with this computer player.
     *
     * @return the line
     */
    //@ ensures \result != null;
    public Line getLine(){
        return line;
    }
}
