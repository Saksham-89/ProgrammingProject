package ProgrammingProject;

import java.util.List;
import java.util.Random;

public class ComputerPlayer {

    /**
     * Represents a computer-controlled player in a game.
     * This class encapsulates the logic for a computer player to make decisions and execute moves.
     */

    private int playerNumber;

    /**
     * Constructs a ComputerPlayer with a specified player number.
     *
     * @param playerNumber The player number to assign to this computer player.
     */

    public ComputerPlayer(int playerNumber) {
        this.playerNumber = playerNumber;
    }

    /**
     * Retrieves the player number of this computer player.
     *
     * @return The player number.
     */

    public int getPlayerNumber() {
        return playerNumber;
    }

    /**
     * Determines and executes a move for the computer player.
     * The method simulates a thinking delay and then chooses a move randomly from the list of valid moves.
     *
     * @param validMoves A list of integers representing the valid moves the player can make.
     * @return The chosen move, represented as an integer. Returns -1 if no valid moves are available.
     */

    public int makeMove(List<Integer> validMoves) {
        System.out.println("Computer Player " + playerNumber + " is thinking...");

        // Simulate some thinking time (you can customize this based on the difficulty level)
        try {
            Thread.sleep(1000);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }

        // Choose a random valid move
        return chooseRandomMove(validMoves);
    }

    /**
     * Chooses a random move from a list of valid moves.
     *
     * @param validMoves A list of integers representing valid moves.
     * @return A randomly chosen move, or -1 if the list of valid moves is empty.
     */

    private int chooseRandomMove(List<Integer> validMoves) {
        if (validMoves.isEmpty()) {
            return -1; // No valid moves available
        }

        Random random = new Random();
        int randomIndex = random.nextInt(validMoves.size());
        return validMoves.get(randomIndex);
    }
}
