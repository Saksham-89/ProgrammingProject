package ProgrammingProject.ai;

import ProgrammingProject.model.DotsAndBoxesGame;
import ProgrammingProject.model.DotsAndBoxesMove;
import java.util.Random;

public class NaiveStrategy implements Strategy {

    @Override
    public String getName() {
        return "Naive Strategy";
    }

    @Override
    public DotsAndBoxesMove determineMove(DotsAndBoxesGame game) {
        Random random = new Random();
        int randomNumber = random.nextInt(game.getValidMoves().size());
        System.out.println(game.getValidMoves().get(randomNumber));
        return game.getValidMoves().get(randomNumber);
    }
}
