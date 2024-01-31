package ProgrammingProject.tests;


import ProgrammingProject.model.*;
import java.util.ArrayList;
import java.util.List;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

public class DotsAndBoxesGameTest {
    private DotsAndBoxesGame game;
    private DotsAndBoxesMove move1;
    private DotsAndBoxesMove move2;

    @BeforeEach
    public void setUp() {
        Player[] players = new Player[]{new HumanPlayer("S", Line.BLUE), new HumanPlayer("M", Line.RED)};
        this.game = new DotsAndBoxesGame(players, 3);
        this.move1 = new DotsAndBoxesMove(Line.BLUE, 0 ,1);
        this.move2 = new DotsAndBoxesMove(Line.RED, 1, 2);
    }

    @Test
    public void testGameStartsWithFirstPlayer() {
        assertEquals(0, game.getCurrentPlayer());
    }

    @Test
    public void testDoMove(){
        DotsAndBoxesMove move = new DotsAndBoxesMove(Line.BLUE, 0,1);
        assertTrue(game.isValidDotsAndBoxesMove(move));
    }

    @Test
    public void testInvalidMove(){
        DotsAndBoxesMove move = new DotsAndBoxesMove(Line.BLUE, 0 ,1);
        game.doMove(move);
        assertFalse(game.isValidDotsAndBoxesMove(move));
    }

    @Test
    public void testAlternateMoves(){
        game.doMove(move1);
        assertEquals(1, game.getCurrentPlayer());
        game.doMove(move2);
        assertEquals(0, game.getCurrentPlayer());
    }


}
