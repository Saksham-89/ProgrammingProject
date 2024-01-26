package ProgrammingProject.ai;

import ProgrammingProject.model.*;

public class ComputerPlayer extends AbstractPlayer {

    private Line line;
    private ProgrammingProject.ai.Strategy strategy;

    public ComputerPlayer(Line line, ProgrammingProject.ai.Strategy strategy){
        super(strategy.getName());
        this.line = line;
        this.strategy = strategy;
    }

    public DotsAndBoxesMove determineMove(DotsAndBoxesGame game){
        return strategy.determineMove(game);
    }

    public Strategy getStrategy(){
        return strategy;
    }

    public Line getLine(){
        return line;
    }
}
