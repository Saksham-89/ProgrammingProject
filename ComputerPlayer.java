package ProgrammingProject;

import java.util.List;
import java.util.Random;

public class ComputerPlayer {

    private int playerNumber;

    public ComputerPlayer(int playerNumber) {
        this.playerNumber = playerNumber;
    }

    public int getPlayerNumber() {
        return playerNumber;
    }

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

    private int chooseRandomMove(List<Integer> validMoves) {
        if (validMoves.isEmpty()) {
            return -1; // No valid moves available
        }

        Random random = new Random();
        int randomIndex = random.nextInt(validMoves.size());
        return validMoves.get(randomIndex);
    }
}
