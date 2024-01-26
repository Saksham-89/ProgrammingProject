package ProgrammingProject.ui;

import ProgrammingProject.ai.ComputerPlayer;
import ProgrammingProject.ai.NaiveStrategy;
import ProgrammingProject.ai.SmartStrategy;
import ProgrammingProject.ai.Strategy;
import ProgrammingProject.model.*;
import java.util.InputMismatchException;
import java.util.Scanner;
import java.util.function.Function;

public class DotsAndBoxesTUI {

    private static final String NAIVE_STRATEGY_KEY = "-N";
    private static final String SMART_STRATEGY_KEY = "-S";


    public static void main(String[] args) {
        DotsAndBoxesTUI tui = new DotsAndBoxesTUI();
        tui.run();
    }

    public void run(){
        Scanner input = new Scanner(System.in);
        System.out.println("Welcome to Dots And Boxes Game!");
        System.out.println("What are the names of the players?");

        Player player1 = createPlayer(input, "Player 1", Line.BLUE);
        Player player2 = createPlayer(input, "Player 2", Line.RED);
        Player[] players = {player1, player2};

        int DIM = getDimension(input);
        DotsAndBoxesGame game = new DotsAndBoxesGame(players, DIM);

        while (!(game.gameOver())){
           processTurn(game, input);
        }

        displayResults(game);

    }

    private Player createPlayer(Scanner input, String playerLabel, Line line) {
        System.out.print(playerLabel + ": ");
        String playerInput = input.nextLine();
        switch (playerInput) {
            case "-N":
                return new ProgrammingProject.ai.ComputerPlayer(line, new NaiveStrategy());
            case "-S":
                return new ComputerPlayer(line, new SmartStrategy());
            default:
                return new ProgrammingProject.model.HumanPlayer(playerInput, line);
        }
    }

    private int getDimension(Scanner input) {
        int dim;
        while (true) {
            System.out.println("Choose your dimension: ");
            try {
                dim = input.nextInt();
                if (dim <= 0) {
                    throw new IllegalArgumentException("Dimension must be positive");
                }
                return dim;
            } catch (InputMismatchException | IllegalArgumentException e) {
                System.out.println("Invalid input. Please enter a positive integer.");
                input.nextLine();
            }
        }
    }

    private int[] parseMove(String inputtedMove) {
        String[] split = inputtedMove.split("-");
        if (split.length != 2) {
            System.out.println("Not a valid index");
            return null;
        }
        try {
            int start = Integer.parseInt(split[0]);
            int end = Integer.parseInt(split[1]);
            return new int[] { start, end };
        } catch (NumberFormatException n) {
            System.out.println("Invalid format try again");
            return null;
        }
    }

    private void executeMove(DotsAndBoxesGame game, int start, int end) {
        Move newMove = new DotsAndBoxesMove(game.getLine(game.getTurn()), start, end);
        if (game.validMove(newMove)) {
            game.doMove(newMove);
        } else {
            System.out.println("Invalid move");
        }
    }

    private void processTurn(DotsAndBoxesGame game, Scanner input) {
        Player currentPlayer = game.getTurn();
        System.out.println(game.toString());

        if (currentPlayer instanceof HumanPlayer) {
            System.out.print("Enter your move: ");
            String move = input.nextLine();
            int[] movePoints = parseMove(move);
            if (movePoints != null) {
                executeMove(game, movePoints[0], movePoints[1]);
            }
        } else {
            ProgrammingProject.ai.ComputerPlayer ai = (ComputerPlayer) currentPlayer;
            Strategy strategy = ai.getStrategy();
            String inputtedMove = strategy.determineMove(game).toString();
            int[] movePoints = parseMove(inputtedMove);
            if (movePoints != null) {
                executeMove(game, movePoints[0], movePoints[1]);
            }
        }
    }

    private void displayResults(DotsAndBoxesGame game) {
        System.out.println(game.getBoard());

        Player winner = game.getWinner();
        if (winner == null) {
            System.out.println("It's a draw.");
        } else {
            System.out.println("The winner is " + winner + "!");
        }
    }



}
