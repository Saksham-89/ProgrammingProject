package ProgrammingProject.ai;


import ProgrammingProject.model.DotsAndBoxesGame;
import ProgrammingProject.model.DotsAndBoxesMove;


public interface Strategy {
    String getName();
    DotsAndBoxesMove determineMove(DotsAndBoxesGame game);
}
