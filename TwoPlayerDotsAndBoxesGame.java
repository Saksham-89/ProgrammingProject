package ProgrammingProject;
import java.util.List;
import java.util.Scanner;

public class TwoPlayerDotsAndBoxesGame {

    public static void main(String[] args) {
        Scanner scanner = new Scanner(System.in);

        // Create a new game
        DotsAndBoxesGame game = new DotsAndBoxesGame();

        while (!game.isGameOver()) {
            System.out.println("Current Board:");
            printBoard(game.getBoard());
            System.out.println("Player " + game.getCurrentPlayer() + "'s turn:");

            // Handle the current player's move
            if (game.getCurrentPlayer() == 1) {
                handleHumanPlayerMove(game, scanner);
            } else {
                handleComputerPlayerMove(game);
            }
        }

        System.out.println("Game Over!");
        System.out.println("Final Scores:");
        System.out.println("Player 1: " + game.getPlayer1Score());
        System.out.println("Player 2: " + game.getPlayer2Score());

        scanner.close();
    }

    private static void handleHumanPlayerMove(DotsAndBoxesGame game, Scanner scanner) {
        List<Integer> validMoves = game.getValidMoves();
        System.out.println("Valid moves: " + validMoves);

        int chosenMove;
        do {
            chosenMove = getUserInput(scanner);
            if (!validMoves.contains(chosenMove)) {
                System.out.println("Invalid move. Please choose a valid move from the list.");
            }
        } while (!validMoves.contains(chosenMove));

        game.doMove(chosenMove);
    }

    private static void handleComputerPlayerMove(DotsAndBoxesGame game) {
        List<Integer> validMoves = game.getValidMoves();
        System.out.println("Computer Player " + game.getCurrentPlayer() + " is thinking...");

        // Simulate some thinking time (you can customize this based on the difficulty level)
        try {
            Thread.sleep(1000);
        } catch (InterruptedException e) {
            e.printStackTrace();
        }

        // Choose a random valid move for the computer player
        int chosenMove = chooseRandomMove(validMoves);
        System.out.println("Computer Player " + game.getCurrentPlayer() + " chose move: " + chosenMove);
        game.doMove(chosenMove);
    }

    private static int chooseRandomMove(List<Integer> validMoves) {
        if (validMoves.isEmpty()) {
            return -1; // No valid moves available
        }

        return validMoves.get((int) (Math.random() * validMoves.size()));
    }

    private static int getUserInput(Scanner scanner) {
        System.out.print("Enter your move: ");
        while (!scanner.hasNextInt()) {
            System.out.println("Invalid input. Please enter a number.");
            scanner.next(); // Consume the invalid input
        }
        return scanner.nextInt();
    }

    private static void printBoard(Board board) {
        for (int row = 0; row < Board.DIM; row++) {
            for (int col = 0; col < Board.DIM; col++) {
                System.out.print(".   ");
                if (col < Board.DIM - 1 && board.isLineDrawn(row * (Board.DIM - 1) + col, true)) {
                    System.out.print("-   ");
                } else {
                    System.out.print("    ");
                }
            }
            System.out.println();

            if (row < Board.DIM - 1) {
                for (int col = 0; col < Board.DIM; col++) {
                    if (board.isLineDrawn(row * (Board.DIM - 1) + col, false)) {
                        System.out.print("|   ");
                    } else {
                        System.out.print("    ");
                    }
                    System.out.print("    ");
                }
                System.out.println();
            }
        }
    }


}
