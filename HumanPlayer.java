package ProgrammingProject;

import java.util.Scanner;

/**
 * Represents a human player in the Dots and Boxes game.
 * This class handles the interactions for a human player to choose moves during the game.
 */

public class HumanPlayer implements Player {

    /**
     * Constructs a HumanPlayer with a specified player number.
     *
     * @param playerNumber The number that identifies this human player.
     */


    private int playerNumber;
    private Scanner scanner;

    /**
     * Constructs a HumanPlayer with a specified player number.
     *
     * @param playerNumber The number that identifies this human player.
     */

    public HumanPlayer(int playerNumber) {
        this.playerNumber = playerNumber;
        this.scanner = new Scanner(System.in);
    }

    /**
     * Prompts the human player to choose a move in the Dots and Boxes game.
     * The method asks for input and validates it to ensure it is a valid move.
     *
     * @param game The instance of DotsAndBoxesGame for which the move is being made.
     * @return The chosen move, represented as an integer.
     */
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

    /**
     * Checks if a given move is valid in the context of the current game.
     * A move is considered valid if it is within the bounds of the game board and has not been made yet.
     *
     * @param move The move to be checked.
     * @param game The instance of DotsAndBoxesGame to check the validity against.
     * @return true if the move is valid, false otherwise.
     */

    private boolean isValidMove(int move, DotsAndBoxesGame game) {
        return game.isValidMove(move);
    }
}
