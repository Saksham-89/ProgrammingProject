package ProgrammingProject.model;

import java.util.ArrayList;
import java.util.List;

public class DotsAndBoxesGame implements Game {

    private final Board board;
    private final Player[] players;
    private int currentPlayer;

    public DotsAndBoxesGame(Player[] players, int DIM){
        this.players = players;
        this.currentPlayer = 0;
        this.board = new Board(DIM);
    }

    public Line getLine(Player player){
        if (player == players[0]){
            return Line.BLUE;
        }
        return Line.RED;
    }
    public Board getBoard(){return board;}

    @Override
    public boolean gameOver() {
        return board.gameOver();
    }

    @Override
    public Player getTurn() {
        return players[currentPlayer];
    }

    @Override
    public Player getWinner() {
        if (!board.hasWinner()) {
            return null; // No winner yet
        }
        int scorePlayer1 = board.getScore(Line.BLUE);
        int scorePlayer2 = board.getScore(Line.RED);

        if (scorePlayer1 > scorePlayer2) {
            return players[0];
        } else if (scorePlayer2 > scorePlayer1) {
            return players[1];
        }
        return null; // It's a draw if scores are equal
    }

    @Override
    public List<DotsAndBoxesMove> getValidMoves() {
        List<DotsAndBoxesMove> validMoves = new ArrayList<>();
        int dimension = board.getDIM();

        // Loop through each dot on the board to check potential moves
        for (int i = 0; i < dimension * dimension; i++) {
            int row = i / dimension;
            int col = i % dimension;

            // Check for horizontal line: Ensures the line doesn't wrap around the right edge of the board
            if (col < dimension - 1) {
                int end = i + 1; // The dot next to the current dot horizontally
                // If there's no line between these two dots, it's a valid move
                if (board.getLine(i, end) == Line.EMPTY) {
                    validMoves.add(new DotsAndBoxesMove(getLine(getTurn()), i, end));
                }
            }

            // Check for vertical line: Ensures the line doesn't go beyond the bottom edge of the board
            if (row < dimension - 1) {
                int end = i + dimension; // The dot directly below the current dot
                // If there's no line between these two dots, it's a valid move
                if (board.getLine(i, end) == Line.EMPTY) {
                    validMoves.add(new DotsAndBoxesMove(getLine(getTurn()), i, end));
                }
            }
        }

        return validMoves; // Return the list of all valid moves
    }


    @Override
    public boolean validMove(Move move) {
        if (!(move instanceof DotsAndBoxesMove)) {
            return false; // Early return if move is not an instance of DotsAndBoxesMove
        }

        DotsAndBoxesMove dotsAndBoxesMove = (DotsAndBoxesMove) move;
        int start = dotsAndBoxesMove.getStart();
        int end = dotsAndBoxesMove.getEnd();
        int dimension = board.getDIM();
        int boardSize = dimension * dimension;

        // Check if start and end are within the board's boundaries
        if (start < 0 || start >= boardSize || end < 0 || end >= boardSize) {
            return false;
        }

        // Determine the type of move (horizontal or vertical)
        int difference = Math.abs(start - end);
        if (difference == 1) {
            // Horizontal move: check for wrapping around the right edge
            return isHorizontalMoveValid(start, end, dimension);
        } else if (difference == dimension) {
            // Vertical move
            return board.getLine(start, end) == Line.EMPTY;
        }
        return false;
    }

    @Override
    public void doMove(Move move) {
        if (isValidDotsAndBoxesMove(move)) {
            DotsAndBoxesMove dotsAndBoxesMove = (DotsAndBoxesMove) move;

            if (dotsAndBoxesMove.getIndex() == 0) {
                setLineAndCheckSquare(dotsAndBoxesMove.getStart(), dotsAndBoxesMove.getEnd(), dotsAndBoxesMove.getLine());
            } else {
                List<Integer> linePoints = board.getPoints(dotsAndBoxesMove.getIndex());
                dotsAndBoxesMove.setStart(linePoints.get(0));
                dotsAndBoxesMove.setEnd(linePoints.get(1));
                setLineAndCheckSquare(dotsAndBoxesMove.getStart(), dotsAndBoxesMove.getEnd(), dotsAndBoxesMove.getLine());
            }
        }
    }

    private boolean isValidDotsAndBoxesMove(Move move) {
        return move instanceof DotsAndBoxesMove && validMove(move);
    }
    private void setLineAndCheckSquare(int start, int end, Line line) {
        board.doMove(start, end, line);
        if (!board.checkSquare(start, end)) {
            currentPlayer = (currentPlayer + 1) % 2;
        }
    }



    private boolean isHorizontalMoveValid(int start, int end, int dimension) {
        if ((start % dimension) == (dimension - 1)) {
            return false; // Invalid if wrapping around the right edge
        }
        return board.getLine(start, end) == Line.EMPTY;
    }

    @Override
    public String toString(){
        if (getLine(getTurn()) == Line.BLUE){
            return String.format(players[currentPlayer] + "'s score: " + board.getScore(Line.BLUE) + "\n" + players[currentPlayer + 1] + "'s score: " + board.getScore(Line.RED) + "\n" + "\u001B[34m" + players[currentPlayer] +  "'s turn\n" + "\u001B[0m"  +  "\n" + players[currentPlayer] + "'s valid moves are: " + getValidMoves() + "\n\n"  + getBoard() + "\n" + "What is your move in format [start-number]?\n" );
        }
        return String.format(players[currentPlayer - 1] + "'s score: " + board.getScore(Line.BLUE) + "\n" + players[currentPlayer] + "'s score: " + board.getScore(Line.RED) + "\n" + "\u001B[31m" + players[currentPlayer] +  "'s turn\n" + "\u001B[0m"  +  "\n" + players[currentPlayer] + "'s valid moves are: " + getValidMoves() + "\n\n"  + getBoard() + "\n" + "What is your move in format [start-number]?\n" );
    }

}
