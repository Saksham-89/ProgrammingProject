package ProgrammingProject.ui;

import ProgrammingProject.ai.ComputerPlayer;
import ProgrammingProject.ai.NaiveStrategy;
import ProgrammingProject.ai.SmartStrategy;
import ProgrammingProject.ai.Strategy;
import ProgrammingProject.model.*;
import java.util.InputMismatchException;
import java.util.Scanner;
import java.util.function.Function;

/**
 * Represents the text user interface for the Dots and Boxes game.
 * This class handles user interactions, game setup, and the main game loop.
 */
public class DotsAndBoxesTUI {

    private static final String NAIVE_STRATEGY_KEY = "-N";
    private static final String SMART_STRATEGY_KEY = "-S";

    private int DIM;

    /**
     * The main method to start the game.
     *
     * @param args Command line arguments (not used).
     */
    public static void main(String[] args) {
        DotsAndBoxesTUI tui = new DotsAndBoxesTUI();
        tui.run();
    }
    /**
     * Runs the main game loop, handling game setup and turns.
     */
    public void run(){
        Scanner input = new Scanner(System.in);
        System.out.println("Welcome to Dots And Boxes Game!");
        System.out.println("What are the names of the players?");

        Player player1 = createPlayer(input, "Player 1", Line.BLUE);
        Player player2 = createPlayer(input, "Player 2", Line.RED);
        Player[] players = {player1, player2};

        DIM = getDimension(input);
        DotsAndBoxesGame game = new DotsAndBoxesGame(players, DIM);

        while (!(game.gameOver())){
           processTurn(game, input);
        }

        displayResults(game);

    }
    /**
     * Creates a player based on user input. Allows selection between human and AI players.
     *
     * @param input Scanner for reading user input.
     * @param playerLabel Label for the player (e.g., "Player 1").
     * @param line The line color associated with the player.
     * @return A Player instance corresponding to the user's choice.
     */
    /*@
      @ requires input != null && playerLabel != null && (line == Line.BLUE || line == Line.RED);
      @ ensures \result instanceof HumanPlayer || \result instanceof ComputerPlayer;
      @*/
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
    /**
     * Prompts the user to enter the game board dimension and validates the input.
     *
     * @param input Scanner for reading user input.
     * @return A positive integer representing the dimension of the game board.
     */
    /*@
      @ requires input != null;
      @ ensures \result > 0;
      @ signals (InputMismatchException e) true;
      @*/
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
    /**
     * Executes a move based on user input.
     *
     * @param game The current game instance.
     * @param userInput The index of the move chosen by the user.
     */
    /*@
      @ requires game != null && userInput > 0 && userInput <= DIM * DIM;
      @ ensures true;
      @*/
    private void executeMove(DotsAndBoxesGame game, int userInput) {
        // Adjust for 0-based indexing used internally.
        int index = userInput - 1;
        // Correctly calculate total moves for horizontal and vertical.
        int totalMoves = DIM * (DIM - 1) * 2; // Total moves (both horizontal and vertical)
        int totalHorizontalMoves = DIM * (DIM - 1); // Just horizontal moves

        int start, end;

        if (index < totalHorizontalMoves) { // Horizontal move
            int effectiveRow = index / (DIM - 1);
            int effectiveCol = index % (DIM - 1);
            start = effectiveRow * DIM + effectiveCol;
            end = start + 1;
        } else if (index < totalMoves) { // Vertical move, checking if index is within total moves range
            index -= totalHorizontalMoves; // Adjust index for vertical calculation
            int effectiveRow = index / (DIM - 1);
            int effectiveCol = index % (DIM - 1);
            start = effectiveCol * DIM + effectiveRow;
            end = start + DIM;
        } else {
            // If the move is out of range, it's invalid.
            System.out.println("Invalid move");
            return;
        }

        Move newMove = new DotsAndBoxesMove(game.getLine(game.getTurn()), start, end);

        if (game.validMove(newMove)) {
            game.doMove(newMove);
        } else {
            System.out.println("Invalid move");
        }
    }
    /**
     * Processes a turn for the current player.
     *
     * @param game The current game instance.
     * @param input Scanner for reading user input.
     */
    /*@
      @ requires game != null && input != null;
      @ ensures true;
      @*/
    private void processTurn(DotsAndBoxesGame game, Scanner input) {
        Player currentPlayer = game.getTurn();
        System.out.println(game.toString());

        if (currentPlayer instanceof HumanPlayer) {
            System.out.print("Enter your move: ");
            while (!input.hasNextInt()) {
                System.out.println("Please enter an integer.");
                input.next();
            }
            int move = input.nextInt();
            executeMove(game, move);
        } else {
            ProgrammingProject.ai.ComputerPlayer ai = (ComputerPlayer) currentPlayer;
            Strategy strategy = ai.getStrategy();
            DotsAndBoxesMove inputtedMove = strategy.determineMove(game);
            executeAIMove(game, inputtedMove);
        }
    }
    /**
     * Specifically executes a move for an AI player.
     *
     * @param game The current game instance.
     * @param move The move determined by the AI's strategy.
     */
    /*@
      @ requires game != null && move != null;
      @ ensures true;
      @*/
    private void executeAIMove(DotsAndBoxesGame game, DotsAndBoxesMove move){
        if (game.validMove(move)){
            game.doMove(move);
        } else {
            System.out.println("Invalid move");
        }
    }
    /**
     * Displays the game results, including the final board state and the winner, if any.
     *
     * @param game The completed game instance.
     */
    /*@
      @ requires game != null;
      @ ensures true;
      @*/
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
