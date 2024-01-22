package ProgrammingProject;

import java.util.Scanner;

public class HumanPlayer implements Player {

    private int playerNumber;
    private Scanner scanner;

    public HumanPlayer(int playerNumber) {
        this.playerNumber = playerNumber;
        this.scanner = new Scanner(System.in);
    }

    @Override
    public int chooseMove(DotsAndBoxesGame game) {
        System.out.println("Player " + playerNumber + ", enter your move (0-" + (Board.DIM * Board.DIM - 1) + "): ");
        int move = -1;

        while (!isValidMove(move, game)) {
            try {
                move = Integer.parseInt(scanner.nextLine());
            } catch (NumberFormatException e) {
                System.out.println("Invalid input. Please enter a number.");
            }

            if (!isValidMove(move, game)) {
                System.out.println("Invalid move. Please choose a valid, unfilled field.");
            }
        }

        return move;
    }

    private boolean isValidMove(int move, DotsAndBoxesGame game) {
        return game.isValidMove(move);
    }
}
