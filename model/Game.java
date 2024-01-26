package ProgrammingProject.model;

import java.util.List;

public interface Game {

    boolean gameOver();

    Player getTurn();

    Player getWinner();

    List<? extends Move> getValidMoves();

    boolean validMove(Move move);

    void doMove(Move move);
}
