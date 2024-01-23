package ProgrammingProject;

import java.util.List;
import java.util.Scanner;

public class DotsAndBoxesApp {

    public static void main(String[] args) {
        DotsAndBoxesGame game = new DotsAndBoxesGame();
        Scanner scanner = new Scanner(System.in);

        while (!game.isGameOver()) {
            System.out.println("Current Board:");
            printBoard(game.getBoard());
            System.out.println("Player " + game.getCurrentPlayer() + "'s turn:");

            if (game.getCurrentPlayer() == 1) {
                // Human player's turn
                handleHumanPlayerMove(game, scanner);
            } else {
                // Computer player's turn
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
        ComputerPlayer computerPlayer = new ComputerPlayer(game.getCurrentPlayer());
        List<Integer> validMoves = game.getValidMoves();
        int chosenMove = computerPlayer.makeMove(validMoves);
        game.doMove(chosenMove);
    }

    private static int getUserInput(Scanner scanner) {
        System.out.print("Enter your move: ");
        while (!scanner.hasNextInt()) {
            System.out.println("Invalid input. Please enter a number.");
            scanner.next(); // Consume the invalid input
        }
        return scanner.nextInt();
    }

    // Modified method to print the board with lines
    private static void printBoard(Board board) {
        for (int row = 0; row < Board.DIM * 2 - 1; row++) {
            for (int col = 0; col < Board.DIM * 2 - 1; col++) {
                if (row % 2 == 0 && col % 2 == 0) {
                    System.out.print(".   ");
                } else if (row % 2 == 0 && col % 2 == 1) {
                    System.out.print(board.isLineDrawn(row / 2 * (Board.DIM - 1) + col / 2, true) ? "-   " : "    ");
                } else if (row % 2 == 1 && col % 2 == 0) {
                    System.out.print(board.isLineDrawn((row - 1) / 2 * (Board.DIM - 1) + col / 2, false) ? "|   " : "    ");
                } else {
                    System.out.print("    ");
                }
            }
            System.out.println();
        }
    }
}
