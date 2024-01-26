package ProgrammingProject.model;

import java.util.Scanner;

public class HumanPlayer extends AbstractPlayer {

    private Line line;

    public HumanPlayer(String name, Line line){
        super(name);
        this.line = line;
    }

    @Override
    public DotsAndBoxesMove determineMove(DotsAndBoxesGame game) {
        Scanner input = new Scanner(System.in);
        try {
            System.out.print("Enter your move: ");
            String move = input.nextLine();
            String[] splitMove = move.split("-");

            if (splitMove.length != 2) {
                System.out.println("Invalid move format. Please input as 'start-end'.");
                return null;
            }

            int start = Integer.parseInt(splitMove[0].trim());
            int end = Integer.parseInt(splitMove[1].trim());

            DotsAndBoxesMove newMove = new DotsAndBoxesMove(line, start, end);

            if (!game.validMove(newMove)) {
                System.out.println("Invalid move. Please try again.");
                return null;
            }

            return newMove;
        } catch (NumberFormatException e) {
            System.out.println("Invalid number format. Please input integers in 'start-end' format.");
            return null;
        }
    }

}
