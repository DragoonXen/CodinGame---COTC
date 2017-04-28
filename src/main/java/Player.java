import java.io.File;
import java.io.IOException;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.ListIterator;
import java.util.Scanner;

class Player {

	public static void main(String args[]) throws IOException {
		if (args.length == 1) {
			Solution.in = new Scanner(new File(args[0]));
		} else if (args.length > 1) {
			Solution.WAIT_ACTION_SCORE = Integer.parseInt(args[0]);
			Solution.FAST_MOVE_SCORE_ADD = Integer.parseInt(args[1]);
			Solution.SLOW_MOVE_SCORE = Integer.parseInt(args[2]);
			Solution.ROTATE_WHILE_MOVE_SCORE = Integer.parseInt(args[3]);
			Solution.COLLISION_PENALTY = Integer.parseInt(args[4]);
			Solution.CLOSE_DISTANCE_PENALTY = Integer.parseInt(args[5]);
			Solution.ENEMY_COLLISION_BONUS = Integer.parseInt(args[6]);
			Solution.POSSIBLE_MINE_PENALTY = Integer.parseInt(args[7]);
			Solution.RUM_COUNT_MULTIPLIER = Integer.parseInt(args[8]);
			Solution.BARREL_NEAR_SCORE = Integer.parseInt(args[9]);
			Solution.BARREL_NEAR_DISTANCE_LOWERING_MULT = Integer.parseInt(args[10]);
			Solution.DIFFERENCE_DISTANCE_TO_BARREL_MULT = Integer.parseInt(args[11]);
			Solution.EXCESS_RUM_PENALTY = Integer.parseInt(args[12]);
			Solution.POSITIONS_SCORE = Integer.parseInt(args[13]);
		}
		new Player();
	}

	public Player() {
		new Solution().run();
	}

	private final static int SHOOT_CD = 2;
	private final static int MINE_CD = 5;
	private final static int MINE_VISIBILITY_RANGE = 5;
	private static final int FIRE_DISTANCE_MAX = 10;
	private static final int LOW_DAMAGE = 25;
	private static final int HIGH_DAMAGE = 50;
	private static final int MINE_DAMAGE = 25;
	private static final int NEAR_MINE_DAMAGE = 10;
	private final static int FIELD_WIDTH = 23;
	private final static int FIELD_HEIGHT = 21;
	private final static Barrel TERMINATE_BARREL = new Barrel(-1, 0, 0, 0);

	public static class Solution {

		static Scanner in = new Scanner(System.in);

		private List<Barrel> barrels = new ArrayList<>();
		private List<Ship> enemyShips = new ArrayList<>();
		private List<Ship> myShips = new ArrayList<>();
		private static List<Ship> allShips = new ArrayList<>();
		private List<Ball> balls = new ArrayList<>();
		private List<Mine> mines = new ArrayList<>();
		private final static Ship pseudoShip = new Ship(0, 5, 5, 0, 0, 0, 0);

		Ship[] prevStep = new Ship[6];
		String[] shipAction = new String[6];
		int[] shipScore = new int[7];
		boolean out = false;

		Barrel creationBarrel;
		Ship shipToDestroy;
		boolean destroyByShooting;

		ShootMineActions[] actionsLists = new ShootMineActions[6];

		Point infPoint = new Point(Integer.MAX_VALUE / 8, Integer.MAX_VALUE / 8);

		boolean test = false;

		boolean isPointMarked(Ship ship, Point point) {
			for (Point p : actionsLists[ship.id].markeredPoints) {
				if (p == point) {
					return true;
				}
			}
			return false;
		}

		int getScoreDiff(Ship ship) {
			return shipScore[ship.id] - shipScore[ship.id + 1];
		}

		ArrayList<ActionType> bkpActions = new ArrayList<>();

		void dfsShipMod(Ship ship) {
			selectedDfsShip = ship;
			dfsScore = -Integer.MAX_VALUE;
			currentDfsScore = 0;
			dfsActions.clear();
			if (test) {
				bkpActions.clear();
				bkpActions.addAll(selectedDfsShip.actions);
			}
			ActionType firstAction = selectedDfsShip.actions.get(0);
			selectedDfsShip.actions.clear();
			lastMark = -1;
			markerPoints.clear();
			if (firstAction == ActionType.WAIT) {
				currentDfsScore += WAIT_ACTION_SCORE; // for wait action
			}
			simulate(1, firstAction);
			int dfsScoreId = ship.id;
			if (test) {
				++dfsScoreId;
				selectedDfsShip.actions.addAll(bkpActions);
				bkpActions.clear();
				bkpActions.addAll(dfsActions);
			} else {
				selectedDfsShip.actions.addAll(dfsActions);
			}
			shipScore[dfsScoreId] = dfsScore;
		}

		void dfsShip(Ship ship) {
			selectedDfsShip = ship;
			dfsScore = -Integer.MAX_VALUE;
			currentDfsScore = 0;
			dfsActions.clear();
			if (test) {
				bkpActions.clear();
				bkpActions.addAll(selectedDfsShip.actions);
			}
			selectedDfsShip.actions.clear();
			lastMark = -1;
			markerPoints.clear();
			dfs(1);
			int dfsScoreId = ship.id;
			if (test) {
				++dfsScoreId;
				selectedDfsShip.actions.addAll(bkpActions);
				bkpActions.clear();
				bkpActions.addAll(dfsActions);
			} else {
				selectedDfsShip.actions.addAll(dfsActions);
			}
			shipScore[dfsScoreId] = dfsScore;
		}

		void dfsShips(int steps, List<Ship> ships) {
			dfsStepsInto = steps + 1;
			for (Ship ship : ships) {
				dfsShip(ship);
				if (!markerPoints.isEmpty()) {
					actionsLists[ship.id].markeredPoints.clear();
					actionsLists[ship.id].markeredPoints.addAll(markerPoints);
				}
			}
		}

		int globalStepNo = 0;

		void run() {
			for (int i = 0; i != 6; ++i) {
				actionsLists[i] = new ShootMineActions();
			}
			while (true) {
				++globalStepNo;
				test = false;
				markEnabled = false;
				read();
				if (shipToDestroy != null) {
					boolean foundToDestroy = false;
					for (Ship ship : myShips) {
						if (shipToDestroy.id == ship.id) {
							foundToDestroy = true;
							break;
						}
					}
					if (!foundToDestroy) {
						shipToDestroy = null;
						creationBarrel = null;
					} else {
						barrels.add(creationBarrel);
						creationBarrel.point.barrel = creationBarrel;
					}
				}
				out = true;

				runBarrelsBfs();
				scoreCalc();

				enemyStep = true;
				dfsShips(3, enemyShips);
				for (Ship ship : enemyShips) {
					ship.actions.clear();
				}
				enemyStep = false;

				dfsStepsInto = 6;
				for (Ship ship : myShips) {
					if (shipToDestroy != null && shipToDestroy.id == ship.id) {
						if (destroyByShooting && ship.speed > 1) {
							shipAction[ship.id] = ActionType.SLOWER.toString();
						}
						continue;
					}
					selectedDfsShip = ship;
					dfsScore = -Integer.MAX_VALUE;
					currentDfsScore = 0;
					dfsActions.clear();
					selectedDfsShip.actions.clear();
					dfs(1);
					selectedDfsShip.actions.addAll(dfsActions);
					if (!dfsActions.isEmpty()) {
						move(ship, dfsActions.get(0));
					} else {
						shipAction[ship.id] = "FATAL";
					}
				}

				enemyStep = true;
				markEnabled = true;
				dfsShips(3, enemyShips);
				test = true;
				for (Ship ship : myShips) {
					if (!shipAction[ship.id].equals("WAIT")) {
						continue;
					}
					int mineScore = -1;
					Ship mineAim = null;
					int shootScore = -1;
					Ship shootAim = null;
					Point aimPt = null;
					int shootStep = 0;
					if (ship.canPlaceMine()) {
						mineScore = 1;
						for (Ship enShip : enemyShips) {
							if (isPointMarked(enShip, ship.preBack)) {
								ship.preBack.mined = true;
								dfsShipMod(enShip);
								actionsLists[enShip.id].updateMine(bkpActions, markerPoints);
								ship.preBack.mined = false;
								int tmpVal = getScoreDiff(enShip);
								debug(String.format("mine decrease ship %d score by %d", enShip.id, tmpVal), DebugType.SHOOTING);
								if (tmpVal > mineScore) {
									mineAim = enShip;
									mineScore = tmpVal;
								}
							}
						}
					}
					if (ship.canChoot()) {
						for (Ship enShip : enemyShips) {
							int step = 1;
							int cnt = -1;
							List<Point> markeredPoint = actionsLists[enShip.id].markeredPoints;
							Iterator<Point> iterator = markeredPoint.iterator();
							if (iterator.hasNext()) {
								iterator.next();
								iterator.next();
								iterator.next();
							}
							Point goodPt = null;
							while (goodPt == null && iterator.hasNext()) {
								goodPt = iterator.next();
								if (++cnt % 3 == 0) {
									step += 1;
								}
								if ((goodPt.hypot(ship.head) + 4) / 3 + 1 != step) {
									goodPt = null;
								}
							}
							if (goodPt != null || enShip.stuckCnt > 3 && ship.head.hypot(enShip.point) <= 10) {
								int tmpVal;
								if (enShip.stuckCnt > 3 && ship.head.hypot(enShip.point) <= 10) {
									goodPt = enShip.point;
									balls.add(new Ball(-1, goodPt.x, goodPt.y, ship.id, step));
									debug(String.format("stuck hardcode shoot ship %d", enShip.id), DebugType.SHOOTING);
									tmpVal = 500;
								} else {
									balls.add(new Ball(-1, goodPt.x, goodPt.y, ship.id, step));
									dfsShipMod(enShip);
									actionsLists[enShip.id].updateShoot(bkpActions, markerPoints);
									tmpVal = getScoreDiff(enShip);
									debug(String.format("shoot decrease ship %d score by %d", enShip.id, tmpVal), DebugType.SHOOTING);
								}
								if (tmpVal > shootScore) {
									aimPt = goodPt;
									shootAim = enShip;
									shootScore = tmpVal;
									shootStep = step;
								}

								balls.remove(balls.size() - 1);
							}
						}
					}
					if (mineScore > shootScore) {
						mine(ship);
						if (mineAim != null) {
							mineAim.actions.clear();
							mineAim.actions.addAll(actionsLists[mineAim.id].mineActione);
							actionsLists[mineAim.id].applyMine();
							shipScore[mineAim.id] -= mineScore;
							ship.preBack.mined = true;
						}
					} else {
						if (shootScore > -1) {
							makeShot(ship, aimPt);
							shootAim.actions.clear();
							shootAim.actions.addAll(actionsLists[shootAim.id].shootActions);
							actionsLists[shootAim.id].applyShoot();
							shipScore[shootAim.id] -= shootScore;
							balls.add(new Ball(-1, aimPt, ship.id, shootStep));
						}
					}
				}

				if (System.currentTimeMillis() - timer > 40) {
					lastUpdateFire();
					continue;
				}

				//self destruct
				int myMaxRum = 0;
				int enemyMaxRum = 0;
				for (Ship ship : myShips) {
					myMaxRum = Math.max(ship.rumCount, myMaxRum);
				}
				for (Ship ship : enemyShips) {
					enemyMaxRum = Math.max(ship.rumCount, enemyMaxRum);
				}
				if (myMaxRum <= enemyMaxRum && myShips.size() > 1 && barrels.isEmpty()) {
					// get next step
					ArrayList<Ship> allShipsCopy = new ArrayList<>(allShips);
					waitDepth = 2;
					simulateWait(1);
					saveDataByList(allShipsCopy);
					for (Ship ship : allShipsCopy) {
						actionsLists[ship.id].nextStep = ship.simulationInfos.getLast();
					}
					for (int i = 0; i != waitDepth; ++i) {
						restoreDataWait();
					}

					for (Ship ship : allShips) {
						ship.actions.clear();
					}
					ArrayList<Ship> myShipsCopy = new ArrayList<>(myShips);
					allShipsCopy = new ArrayList<>(allShips);
					waitDepth = 3;
					simulateWait(1);
					saveDataByList(allShipsCopy);// store last step
					for (Ship ship : allShipsCopy) {
						actionsLists[ship.id].updateSimulationInfo(ship.simulationInfos);
					}
					for (int i = 0; i != waitDepth; ++i) {
						restoreDataWait();
					}

					for (Ship ship : myShipsCopy) {
						if (shipAction[ship.id].startsWith("FIRE")) {
							continue;
						}
						if (ship.rumCount > 26) {
							continue;
						}
						LinkedList<Ship.SimulationInfo> simulationInfo = actionsLists[ship.id].simulationInfo;
						Ship.SimulationInfo last = simulationInfo.getLast();
						if (last.rumCount == 0) {
							Ship.SimulationInfo prevSim = simulationInfo.get(simulationInfo.size() - 2);
							if (prevSim.rumCount > 26) {
								continue;
							}
							int prevRumCount = prevSim.rumCount - 1;
							Point pt = last.point;
							LinkedList<Point> mines = new LinkedList<>();
							if (last.point.mined) {
								last.point.mined = false;
								mines.add(last.point);
							}
							if (last.head.mined) {
								last.head.mined = false;
								mines.add(last.head);
							}
							if (last.back.mined) {
								last.back.mined = false;
								mines.add(last.back);
							}
							Barrel barrel = new Barrel(-1, pt, prevRumCount);
							pt.barrel = barrel;
							barrels.add(barrel);
							runBarrelsBfs();
							for (Point mined : mines) {
								mined.mined = true;
							}
							if (barrelCreationAcceptable(ship)) {
								debug(String.format("self destruct ship with id %d by mine", ship.id), DebugType.SELF_DESTRUCT);
								creationBarrel = barrel;
								shipToDestroy = ship;
								destroyByShooting = false;
								if (!shipAction[ship.id].equals("MINE") && !shipAction[ship.id].equals("WAIT")) {
									shipAction[ship.id] = "WAIT";
									break;
								}
							} else {
								pt.barrel = null;
								barrels.remove(barrel);
							}
						}
					}
					if (creationBarrel == null) {
						for (Ship ship : myShipsCopy) {
							if (shipAction[ship.id].startsWith("FIRE") || ship.shootCd > 0) {
								continue;
							}
							if (ship.rumCount > 32) {
								continue;
							}
							if (ship.rumCount > 27 && ship.speed == 2) {
								continue;
							}
							LinkedList<Ship.SimulationInfo> simulationInfo = actionsLists[ship.id].simulationInfo;
							Ship.SimulationInfo lastSim = simulationInfo.getLast();
							if (lastSim.rumCount < 10) {
								continue;
							}
							boolean mined = shipAction[ship.id].equals("MINE");
							if (mined) {
								ship.preBack.mined = false;
							}

							int prevRumCount = lastSim.rumCount;
							Point pt = lastSim.point;
							if (ship.speed == 2) {
								pt = pt.getNeighbour((lastSim.orientation + 3) % 6);
							}
							if (pt.blocked) {
								continue;
							}
							Barrel barrel = new Barrel(-1, pt, prevRumCount);
							pt.barrel = barrel;
							barrels.add(barrel);
							runBarrelsBfs();
							if (barrelCreationAcceptable(ship)) {
								debug(String.format("self destruct ship with id %d by self shooting", ship.id), DebugType.SELF_DESTRUCT);
								makeShot(ship, pt);
								creationBarrel = barrel;
								shipToDestroy = ship;
								destroyByShooting = true;
								break;
							} else {
								pt.barrel = null;
								barrels.remove(barrel);
							}

							if (mined) {
								ship.preBack.mined = true;
							}

						}
					}
				}

				lastUpdateFire();
			}
		}

		void lastUpdateFire() {
			for (Ship ship : myShips) {
				if (!shipAction[ship.id].equals("WAIT")) {
					continue;
				}
				Ship nearest = null;
				for (Ship enShip : enemyShips) {
					if (enShip.stuckCnt > 3 && (nearest == null || nearest.point.hypot(ship.point) > enShip.point.hypot(ship.point))) {
						nearest = enShip;
					}
				}
				if (nearest != null) {
					debug(String.format("stuck hardcode shoot ship %d", nearest.id), DebugType.SHOOTING);
					makeShot(ship, nearest.point);
				}
			}
		}

		boolean barrelCreationAcceptable(Ship shipToDestroy) {
			int minStepsMy = 100;
			int minStepsMyLast = 100;
			int minStepsMyNext = 100;
			for (Ship myShip : myShips) {
				if (myShip == shipToDestroy) {
					continue;
				}
				int val1 = WayCalc.getWayCalc(myShip).steps;
				int val2 = getLastReachedStep(myShip.id);
				int val3 = WayCalc.getWayCalc(actionsLists[myShip.id].nextStep).steps;
				if (myShip.rumCount < val1 || myShip.rumCount - 2 < val2 || myShip.rumCount - 1 < val3) {
					continue;
				}
				minStepsMy = getMinSteps(minStepsMy, val1);
				minStepsMyLast = getMinSteps(minStepsMyLast, val2);
				minStepsMyNext = getMinSteps(minStepsMyNext, val3);
			}

			int minStepsEnemy = 100;
			int minStepsEnemyLast = 100;
			int minStepsEnemyNext = 100;
			for (Ship enemyShip : enemyShips) {
				int val1 = WayCalc.getWayCalc(enemyShip).steps;
				int val2 = getLastReachedStep(enemyShip.id);
				int val3 = WayCalc.getWayCalc(actionsLists[enemyShip.id].nextStep).steps;
				if (enemyShip.rumCount < val1 && enemyShip.rumCount < val2 && enemyShip.rumCount < val3) {
					continue;
				}
				minStepsEnemy = getMinSteps(minStepsEnemy, val1);
				minStepsEnemyLast = getMinSteps(minStepsEnemyLast, val2);
				minStepsEnemyNext = getMinSteps(minStepsEnemyNext, val3);
			}
			return minStepsEnemy - minStepsMy > 2 && minStepsEnemyLast - minStepsMyLast > 2 && minStepsEnemyNext - minStepsMyNext > 2;
		}

		int getLastReachedStep(int shipId) {
			LinkedList<Ship.SimulationInfo> simulationInfo = actionsLists[shipId].simulationInfo;
			int idx = simulationInfo.size() - 1;
			while (idx != -1) {
				Ship.SimulationInfo item = simulationInfo.get(idx);
				int val = WayCalc.getWayCalcs(item.point)[item.orientation][item.speed].steps;
				if (val != -1) {
					return val;
				}
				--idx;
			}
			return -1;
		}

		int getMinSteps(int first, int second) {
			if (second == -1) {
				return first;
			}
			return Math.min(first, second);
		}

		private List<ActionType> dfsActions = new ArrayList<>();
		private ArrayList<Ship> collisions = new ArrayList<>();
		private ArrayList<Ship> collisionsCopy = new ArrayList<>();
		private ArrayDeque<Point> mineExplosions = new ArrayDeque<>();
		private ArrayDeque<ArrayList<Ship>> shipsList = new ArrayDeque<>();
		private Ship selectedDfsShip;
		private int dfsScore;
		private int currentDfsScore;
		ArrayDeque<Barrel> collectedBarrels = new ArrayDeque<>();
		ArrayDeque<Barrel> eliminationBarrels = new ArrayDeque<>();
		private static int DEATH_PENALTY = 10000000;
		private static int WAIT_ACTION_SCORE = 297;
		private static int FAST_MOVE_SCORE_ADD = 12;
		private static int SLOW_MOVE_SCORE = 128;
		private static int ROTATE_WHILE_MOVE_SCORE = 13;
		private static int COLLISION_PENALTY = 400;
		private static int CLOSE_DISTANCE_PENALTY = 400;

		private static int EXCESS_RUM_PENALTY = 138;
		private static int ENEMY_COLLISION_BONUS = 0;
		private static int POSSIBLE_MINE_PENALTY = 792;
		private static int RUM_COUNT_MULTIPLIER = 138;
		private static int BARREL_NEAR_SCORE = 200;
		private static int BARREL_NEAR_DISTANCE_LOWERING_MULT = 8;
		private static int DIFFERENCE_DISTANCE_TO_BARREL_MULT = 162;
		private static int POSITIONS_SCORE = 63;

		private int dfsStepsInto = 6;

		private boolean enemyStep = false;
		private boolean markEnabled = false;

		private int lastMark = -1;
		private ArrayDeque<Point> markerPoints = new ArrayDeque<>(20);

		private void dfs(int step) {
			if (step == dfsStepsInto || selectedDfsShip.rumCount <= 0) {
				// evaluation and set
				int addScore = 0;
				if (selectedDfsShip.rumCount <= 0) {
					addScore -= DEATH_PENALTY / step;
				}
				WayCalc wayCalc = WayCalc.getWayCalc(selectedDfsShip);
				if (wayCalc.steps > 0) {
					addScore += BARREL_NEAR_SCORE - wayCalc.steps * BARREL_NEAR_DISTANCE_LOWERING_MULT;
				}
				if (wayCalc.barrel != null && wayCalc.barrel.point.barrel != null) {
					int maxDist = -100;
					for (Ship enemyShip : allShips) {
						if (enemyShip.team == Team.ME) {
							continue;
						}
						WayCalc tmp = WayCalc.getWayCalc(enemyShip);
						if (tmp.barrel == wayCalc.barrel) {
							maxDist = Math.max(maxDist, wayCalc.steps - tmp.steps);
						}
					}
					if (maxDist != -100) {
						addScore -= DIFFERENCE_DISTANCE_TO_BARREL_MULT * maxDist;
					}
				}
				currentDfsScore += addScore;
				if (currentDfsScore > dfsScore) {
					if (markEnabled) {
						lastMark = step;
						markerPoints.clear();
					}
					dfsScore = currentDfsScore;
					dfsActions.clear();
					dfsActions.addAll(selectedDfsShip.actions);
				}
				currentDfsScore -= addScore;
				return;
			}
			if (enemyStep && !selectedDfsShip.back.blocked) {
				selectedDfsShip.back.getNeighbour((selectedDfsShip.orientation + 3) % 6).putPossibleMine(step - 1);
			}
			if (selectedDfsShip.actions.isEmpty() || selectedDfsShip.actions.get(selectedDfsShip.actions.size() - 1) != ActionType.WAIT) {
				currentDfsScore += WAIT_ACTION_SCORE; // for wait action
				simulate(step, ActionType.WAIT);
				currentDfsScore -= WAIT_ACTION_SCORE;
			} else {
				simulate(step, ActionType.WAIT);
			}

			if (selectedDfsShip.speed < 2) {
				simulate(step, ActionType.FASTER);
			}
			if (selectedDfsShip.speed > 0) {
				simulate(step, ActionType.SLOWER);
			}
			simulate(step, ActionType.PORT);
			simulate(step, ActionType.STARBOARD);
		}

		void saveData() {
			shipsList.addLast(new ArrayList<>(allShips));
			for (Ship myShip : allShips) {
				myShip.storeSimulationInfo();
				--myShip.rumCount;
			}
			collectedBarrels.add(TERMINATE_BARREL);
			eliminationBarrels.add(TERMINATE_BARREL);
			mineExplosions.add(infPoint);
		}

		void saveDataByList(ArrayList<Ship> ships) {
			shipsList.addLast(new ArrayList<>(ships));
			for (Ship myShip : ships) {
				myShip.storeSimulationInfo();
				--myShip.rumCount;
			}
			collectedBarrels.add(TERMINATE_BARREL);
			eliminationBarrels.add(TERMINATE_BARREL);
			mineExplosions.add(infPoint);
		}

		void restoreData() {
			selectedDfsShip.actions.remove(selectedDfsShip.actions.size() - 1);
			allShips = shipsList.pollLast();
			for (Ship myShip : allShips) {
				myShip.restoreLastSimulationInfo();
			}
			Barrel currBarrel;
			while ((currBarrel = collectedBarrels.pollLast()) != TERMINATE_BARREL) {
				currBarrel.point.barrel = currBarrel;
			}
			while ((currBarrel = eliminationBarrels.pollLast()) != TERMINATE_BARREL) {
				currBarrel.point.barrel = null;
			}
			Point point;
			while ((point = mineExplosions.pollLast()) != infPoint) {
				point.mined = true;
			}
		}

		void restoreDataWait() {
			allShips = shipsList.pollLast();
			for (Ship myShip : allShips) {
				myShip.restoreLastSimulationInfo();
			}
			Barrel currBarrel;
			while ((currBarrel = collectedBarrels.pollLast()) != TERMINATE_BARREL) {
				currBarrel.point.barrel = currBarrel;
			}
			while ((currBarrel = eliminationBarrels.pollLast()) != TERMINATE_BARREL) {
				currBarrel.point.barrel = null;
			}
			Point point;
			while ((point = mineExplosions.pollLast()) != infPoint) {
				point.mined = true;
			}
		}

		void simulate(int step, ActionType actionType) {
			int currentScoreAdd = 0;
			saveData();
			selectedDfsShip.actions.add(actionType);
			currentScoreAdd += moveShips(step);
			if (selectedDfsShip.speed > 0) {
				currentScoreAdd += SLOW_MOVE_SCORE;
				if (selectedDfsShip.speed > 1) {
					currentScoreAdd += FAST_MOVE_SCORE_ADD;
				}
				if (actionType == ActionType.PORT || actionType == ActionType.STARBOARD) {
					currentScoreAdd += ROTATE_WHILE_MOVE_SCORE;
				}
			}
			explodeBallsAndRemoveEliminated(step);
			currentScoreAdd += selectedDfsShip.rumCount * RUM_COUNT_MULTIPLIER;
			currentScoreAdd += selectedDfsShip.point.pointScore;
			currentDfsScore += currentScoreAdd;
			dfs(step + 1);
			if (lastMark > step) {
				lastMark = step;
				markerPoints.addFirst(selectedDfsShip.back);
				markerPoints.addFirst(selectedDfsShip.head);
				markerPoints.addFirst(selectedDfsShip.point);
			}
			currentDfsScore -= currentScoreAdd;
			restoreData();
		}

		int waitDepth = 3;

		void simulateWait(int step) {
			if (step == waitDepth) {
				return;
			}
			saveData();
			moveShips(step);
			explodeBallsAndRemoveEliminated(step);
			simulateWait(step + 1);
		}

		void explodeBallsAndRemoveEliminated(int step) {
			for (Ball ball : balls) {
				if (ball.stepsToHit == step) {
					Point pt = ball.point;
					if (pt.mined) {
						explodeMine(null, pt);
					} else if (pt.barrel != null) {
						collectedBarrels.addLast(pt.barrel);
						pt.barrel = null;
					} else {
						for (Ship selected : allShips) {
							if (selected.point == pt) {
								selected.damage(HIGH_DAMAGE);
								break;
							}
							if (selected.head == pt || selected.back == pt) {
								selected.damage(LOW_DAMAGE);
								break;
							}
						}
					}
				}
			}
			for (Iterator<Ship> iterator = allShips.iterator(); iterator.hasNext(); ) {
				Ship ship = iterator.next();
				if (ship.rumCount == 0) {
					//eliminationBarrels
					int val = ship.simulationInfos.getLast().rumCount - 1;
					if (val > 0) {
						Barrel barr = new Barrel(-1, ship.point, Math.min(30, val));
						eliminationBarrels.addLast(barr);
					}
					iterator.remove();
				}
			}
		}

		int moveShips(int step) {
			int score = 0;
			boolean possibleMined = false;
			for (Ship ship : allShips) {
				if (ship.actions.size() >= step) {
					switch (ship.actions.get(step - 1)) {
						case FASTER:
							ship.speed = Math.min(2, ship.speed + 1);
							break;
						case SLOWER:
							ship.speed = Math.max(0, ship.speed - 1);
							break;
					}
				}
			}
			for (int speed = 0; speed != 2; ++speed) {
				for (Ship ship : allShips) {
					if (ship.speed > speed) {
						ship.moveFwd();
					}
				}
				for (Ship ship : allShips) {
					if (ship.speed > speed) {
						if (ship == selectedDfsShip) {
							if (!enemyStep && ship.head.possibleMinedStep < step) {
								possibleMined = true;
							}
							boolean collision = false;
							boolean closeDistance = false;
							for (Ship collisionShip : allShips) {
								if (collisionShip == ship) {
									continue;
								}
								if (ship.head == collisionShip.head ||
										ship.head == collisionShip.point ||
										ship.head == collisionShip.back) {
									collisions.add(ship);
									collision = true;
									break;
								} else {
									if (!closeDistance) {
										closeDistance = ship.head.hypot(collisionShip.head) == 1 ||
												ship.head.hypot(collisionShip.back) == 1 ||
												ship.back.hypot(collisionShip.head) == 1 ||
												ship.back.hypot(collisionShip.back) == 1;
									}
								}
							}
							if (ship == selectedDfsShip) {
								if (collision) {
									score -= COLLISION_PENALTY / step;
								} else if (closeDistance) {
									score -= CLOSE_DISTANCE_PENALTY / step;
								}
							}
						} else {
							for (Ship collisionShip : allShips) {
								if (collisionShip == ship) {
									continue;
								}
								if (ship.head == collisionShip.head ||
										ship.head == collisionShip.point ||
										ship.head == collisionShip.back) {
									collisions.add(ship);
									if (ship.team == Team.ENEMY && !enemyStep) {
										score += ENEMY_COLLISION_BONUS;
									}
									break;
								}
							}
						}
					}
				}
				for (Ship ship : collisions) {
					ship.moveBwd();
					ship.speed = 0;
				}
				collisions.clear();
				for (Ship ship : allShips) {
					if (ship.speed > speed) {
						if (ship.head.barrel != null) {
							score += collectBarrel(ship, ship.head, step);
						}
						if (ship.head.mined) {
							explodeMine(ship, ship.head);
						}
					}
				}
			}
			for (Ship ship : allShips) {
				if (ship.actions.size() >= step) {
					switch (ship.actions.get(step - 1)) {
						case PORT:
							collisions.add(ship);
							if (ship == selectedDfsShip && (!enemyStep && (ship.head.possibleMinedStep < step || ship.back.possibleMinedStep < step))) {
								possibleMined = true;
							}
							ship.turnLeft();
							break;
						case STARBOARD:
							collisions.add(ship);
							if (ship == selectedDfsShip && (!enemyStep && (ship.head.possibleMinedStep < step || ship.back.possibleMinedStep < step))) {
								possibleMined = true;
							}
							ship.turnRight();
							break;
					}
				}
			}
			for (Iterator<Ship> iterator = collisions.iterator(); iterator.hasNext(); ) {
				Ship ship = iterator.next();
				boolean noCollisionFound = true;
				for (Ship checkShip : allShips) {
					if (checkShip == ship) {
						continue;
					}
					if (ship.head == checkShip.head || ship.head == checkShip.point || ship.head == checkShip.back ||
							ship.point == checkShip.head || ship.point == checkShip.point || ship.point == checkShip.back ||
							ship.back == checkShip.head || ship.back == checkShip.point || ship.back == checkShip.back) {
						noCollisionFound = false;
						break;
					}
				}
				if (noCollisionFound) {
					collisionsCopy.add(ship);
					iterator.remove();
				}
			}
			for (Ship ship : collisions) {
				switch (ship.actions.get(step - 1)) {
					case PORT:
						ship.turnRight();
						break;
					case STARBOARD:
						ship.turnLeft();
						break;
				}
			}
			for (Ship ship : collisionsCopy) {
				if (ship.head.mined) {
					explodeMine(ship, ship.head);
				} else if (ship.head.barrel != null) {
					score += collectBarrel(ship, ship.head, step);
				}
				if (ship.back.mined) {
					explodeMine(ship, ship.back);
				} else if (ship.back.barrel != null) {
					score += collectBarrel(ship, ship.back, step);
				}
			}
			if (possibleMined) {
				score -= POSSIBLE_MINE_PENALTY;
			}
			collisionsCopy.clear();
			collisions.clear();
			return score;
		}

		int collectBarrel(Ship ship, Point pt, int step) {
			int score = 0;
			if (ship == selectedDfsShip) {
				int val = barrels.size() - collectedBarrels.size() + step;
				if (val > 1 && val <= allShips.size()) {
					int excess = pt.barrel.rumCount - (100 - ship.rumCount);
					if (excess > 0) {
						score -= excess * EXCESS_RUM_PENALTY * (dfsStepsInto - step);
					}
				}
			}
			ship.heal(pt.barrel.rumCount);
			collectedBarrels.addLast(pt.barrel);
			pt.barrel = null;
			return score;
		}

		void explodeMine(Ship victim, Point point) {
			point.mined = false;
			mineExplosions.add(point);
			if (victim != null) {
				victim.damage(MINE_DAMAGE);
			}
			for (Ship selected : allShips) {
				if (selected == victim) {
					continue;
				}
				switch (selected.point.hypot(point)) {
					case 1:
						selected.damage(NEAR_MINE_DAMAGE);
						break;
					case 2:
						if (selected.head.hypot(point) == 1 || selected.back.hypot(point) == 1) {
							selected.damage(NEAR_MINE_DAMAGE);
						}
						break;
				}
			}
		}

		private void printScore() {
			StringBuilder sb = new StringBuilder();
			for (int j = 0; j != FIELD_HEIGHT + 2; ++j) {
				for (int i = 0; i != FIELD_WIDTH + 2; ++i) {
					sb.append(String.format("%4d", Point.GC[i][j].pointScore));
				}
				sb.append("\n");
			}
			System.out.println(sb.toString());
		}

		private void scoreCalc() {
			int cnt = FIELD_WIDTH * FIELD_HEIGHT;
			for (int i = 1; i != FIELD_WIDTH + 1; ++i) {
				for (int j = 1; j != FIELD_HEIGHT + 1; ++j) {
					Point pt = Point.GC[i][j];
					pt.pointScore = 0;
					if (pt.mined) {
						--cnt;
						continue;
					}
					int rez = 0;
					for (int k = 0; k != 6; ++k) {
						Point tmp = pt.getNeighbour(k);
						if (!tmp.mined && !tmp.blocked) {
							rez += 1;
						}
					}
					if (rez != 6) {
						pt.pointScore = POSITIONS_SCORE * rez;
						--cnt;
					}
				}
			}
			LinkedList<Point> updatedPoints = new LinkedList<>();
			while (cnt > 0) {
				for (int i = 1; i != FIELD_WIDTH + 1; ++i) {
					for (int j = 1; j != FIELD_HEIGHT + 1; ++j) {
						Point pt = Point.GC[i][j];
						if (pt.mined || pt.pointScore != 0) {
							continue;
						}
						int rez = 0;
						int tScore = 0;
						for (int k = 0; k != 6; ++k) {
							Point tmp = pt.getNeighbour(k);
							if (tmp.pointScore == 0) {
								tScore += POSITIONS_SCORE * 6;
							} else {
								tScore += tmp.pointScore;
								rez += 1;
							}
						}
						if (rez > 0) {
							pt.tmpScore = tScore / 6;
							--cnt;
							updatedPoints.add(pt);
						}
					}
				}
				for (Point pt : updatedPoints) {
					pt.pointScore = pt.tmpScore;
				}
			}
		}

		private void runBarrelsBfs() {
			WayCalc.cleanAll();
			LinkedList<WayCalc> queue = new LinkedList<>();
			for (Barrel barrel : barrels) {
				if (barrel.point.cellOfDamage()) {
					continue;
				}
				for (int orient = 0; orient != 6; ++orient) {
					pseudoShip.partialUpdateShip(barrel.point, orient);
					if (!pseudoShip.head.cellOfDamage()) {
						if (!pseudoShip.back.cellOfDamage()) {
							for (int speed = 0; speed != 3; ++speed) {
								if (speed == 2 && !pseudoShip.head.blocked && pseudoShip.head.getNeighbour(orient).mined) {
									break;
								}
								WayCalc wayCalc = WayCalc.getWayCalcs(barrel.point)[orient][speed];
								if (wayCalc.steps == -1) {
									wayCalc.steps = 0;
									wayCalc.barrel = barrel;
									queue.add(wayCalc);
								}
							}
						}
						if (!pseudoShip.head.blocked) {
							Point point = pseudoShip.head;
							Point afterHead = point.getNeighbour(orient);
							if (!afterHead.cellOfDamage()) {
								WayCalc wayCalc;
								for (int speed = 0; speed != 3; ++speed) {
									if (speed != 2 || !pseudoShip.point.getNeighbour((orient + 3) % 6).mined) {
										wayCalc = WayCalc.getWayCalcs(point)[(orient + 3) % 6][speed];
										if (wayCalc.steps == -1) {
											wayCalc.steps = 0;
											wayCalc.barrel = barrel;
											queue.add(wayCalc);
										}
									}
									if (speed != 2 || afterHead.blocked || !afterHead.getNeighbour(orient).mined) {
										wayCalc = WayCalc.getWayCalcs(point)[orient][speed];
										if (wayCalc.steps == -1) {
											wayCalc.steps = 0;
											wayCalc.barrel = barrel;
											queue.add(wayCalc);
										}
									}
								}
							}
						}
					}
				}
			}
			while (!queue.isEmpty()) {
				final WayCalc wayPoint = queue.pollFirst();

				int backOrientation = (wayPoint.orientation + 3) % 6;

				// FASTER, SLOWER OR WAIT
				{
					Point from = wayPoint.position;
					boolean acceptable = true;
					for (int i = 0; i != wayPoint.speed; ++i) {
						from = from.getNeighbour(backOrientation);
						if (from.blocked) {
							acceptable = false;
							break;
						}
					}
					if (acceptable) {
						WayCalc[] arr = WayCalc.q[from.x][from.y][wayPoint.orientation];
						switch (wayPoint.speed) {
							case 0:
								if (arr[1].steps == -1) {
									addToQueue(queue, arr[1], wayPoint, ActionType.SLOWER);
								}
								break;
							case 1:
								if (arr[0].steps == -1) {
									addToQueue(queue, arr[0], wayPoint, ActionType.FASTER);
								}
								if (arr[1].steps == -1) {
									addToQueue(queue, arr[1], wayPoint, ActionType.WAIT);
								}
								if (arr[2].steps == -1) {
									addToQueue(queue, arr[2], wayPoint, ActionType.SLOWER);
								}
								break;
							case 2:
								if (arr[1].steps == -1) {
									addToQueue(queue, arr[1], wayPoint, ActionType.FASTER);
								}
								if (arr[2].steps == -1) {
									addToQueue(queue, arr[2], wayPoint, ActionType.WAIT);
								}
								break;
						}
					}
				}

				// PORT then STARBOARD
				for (int i = -1; i != 3; i += 2) {
					int prevOrientation = (wayPoint.orientation + 6 + i) % 6;
					Point prevHeadPoint = wayPoint.position.getNeighbour(prevOrientation);
					if (prevHeadPoint.mined) {
						continue;
					}
					backOrientation = (prevOrientation + 3) % 6;
					Point currPoint = wayPoint.position;
					boolean acceptable = true;
					for (int speed = wayPoint.speed; speed > 0; --speed) {
						Point nextCurrPoint = currPoint.getNeighbour(backOrientation);
						if (nextCurrPoint.mined || nextCurrPoint.blocked) {
							acceptable = false;
							break;
						}
						currPoint = nextCurrPoint;
					}
					if (acceptable && !currPoint.getNeighbour(backOrientation).mined) {
						if (wayPoint.speed == 0 && prevHeadPoint.blocked) {
							for (int speed = 0; speed != 3; ++speed) {
								WayCalc newWayCalc = WayCalc.getWayCalcs(currPoint)[prevOrientation][speed];
								if (newWayCalc.steps == -1) {
									addToQueue(queue, newWayCalc, wayPoint, i == -1 ? ActionType.PORT : ActionType.STARBOARD);
								}
							}
						} else {
							WayCalc newWayCalc = WayCalc.getWayCalcs(currPoint)[prevOrientation][wayPoint.speed];
							if (newWayCalc.steps == -1) {
								addToQueue(queue, newWayCalc, wayPoint, i == -1 ? ActionType.PORT : ActionType.STARBOARD);
							}
						}
					}
				}
			}
		}

		void addToQueue(LinkedList<WayCalc> queue, WayCalc wayCalc, WayCalc prev, ActionType actionType) {
			pseudoShip.partialUpdateShip(wayCalc.position, wayCalc.orientation);
			if (!pseudoShip.head.mined && !pseudoShip.back.mined && !pseudoShip.point.mined) {
				wayCalc.steps = prev.steps + 1;
				wayCalc.nextAction = actionType;
				wayCalc.prevStep = prev;
				wayCalc.barrel = prev.barrel;
				queue.add(wayCalc);
			} else {
				wayCalc.steps = -2;
			}
		}

		boolean mine(Ship actionShip) {
			if (actionShip.mineCd < 1 && !actionShip.back.blocked) {
				Point preBack = actionShip.back.getNeighbour((actionShip.orientation + 3) % 6);
				if (preBack.blocked || preBack.barrel != null || preBack.mined) {
					return false;
				}
				for (Ship ship : allShips) {
					if (ship.head == preBack || ship.point == preBack || ship.back == preBack) {
						return false;
					}
				}
				for (Ship ship : myShips) {
					if (ship == actionShip || ship.speed == 0) {
						continue;
					}
					Point pt = ship.head;
					for (int i = 0; i != ship.speed; ++i) {
						if (pt.blocked) {
							break;
						}
						pt = pt.getNeighbour(ship.orientation);
						if (pt == preBack) {
							return false;
						}
					}
				}

				actionShip.mineCd = MINE_CD;
				shipAction[actionShip.id] = "MINE";
				return true;
			}
			return false;
		}

		void move(Ship ship, ActionType actionType) {
			shipAction[ship.id] = actionType.toString();
		}


		boolean makeShot(Ship turnShip, Point shootPt) {
			if (turnShip.shootCd <= 0 && turnShip.head.hypot(shootPt) <= FIRE_DISTANCE_MAX) {
				turnShip.shootCd = SHOOT_CD;
				shipAction[turnShip.id] = String.format("FIRE %s", shootPt);
				return true;
			}
			return false;
		}

		long timer = System.currentTimeMillis();

		void read() {
			if (out) {
				for (Ship ship : myShips) {
					System.out.println(shipAction[ship.id]);
					if (shipAction[ship.id].equals("MINE")) {
						ship.preBack.mined = false;
					}
					shipAction[ship.id] = "WAIT";
				}
			}
			for (Barrel barrel : barrels) {
				barrel.point.barrel = null;
			}
			barrels.clear();

			{
				for (Iterator<Ball> iterator = balls.iterator(); iterator.hasNext(); ) {
					Ball ball = iterator.next();
					if (--ball.stepsToHit == 0) {
						ball.point.removeBall(ball.id);
						iterator.remove();
					}
				}
			}

			LinkedList<Mine> existMines = new LinkedList<>(mines);
			mines.clear();

			myShips.clear();
			enemyShips.clear();
			debug("processing:" + (System.currentTimeMillis() - timer), DebugType.PROCESSING_TIME);
			int myShipCount = in.nextInt(); // the number of remaining ships
			timer = System.currentTimeMillis();
			int entityCount = in.nextInt(); // the number of entities (e.g. ships, mines or cannonballs)
			debug(String.format("%d\n%d", myShipCount, entityCount), DebugType.INPUT);
			for (int i = 0; i < entityCount; i++) {
				int entityId = in.nextInt();
				String entityType = in.next();

				int x = in.nextInt() + 1;
				int y = in.nextInt() + 1;
				int arg1 = in.nextInt();
				int arg2 = in.nextInt();
				int arg3 = in.nextInt();
				int arg4 = in.nextInt();
				debug(String.format("%d %s %d %d %d %d %d %d", entityId, entityType, x - 1, y - 1, arg1, arg2, arg3, arg4), DebugType.INPUT);
				switch (entityType) {
					case "BARREL":
						Barrel barrel = new Barrel(entityId, x, y, arg1);
						barrel.point.barrel = barrel;
						barrels.add(barrel);
						break;
					case "SHIP": {
						Ship ship = prevStep[entityId];
						if (ship == null) {
							ship = new Ship(entityId, x, y, arg1, arg2, arg3, arg4);
							prevStep[entityId] = ship;
						} else {
							ship = ship.clone();
							ship.updateShip(x, y, arg1, arg2, arg3, arg4);
							ship.updateStuckCnt(prevStep[entityId]);
						}
						if (ship.isMyShip()) {
							myShips.add(ship);
						} else {
							enemyShips.add(ship);
						}
					}
					break;
					case "MINE":
						Mine mine = new Mine(entityId, x, y);
						mines.add(mine);
						if (!existMines.contains(mine)) {
							for (Ship ship : prevStep) {
								if (ship == null || ship.mineCd > 0) {
									continue;
								}
								Point beforeCorma = ship.back.getNeighbour((ship.orientation + 3) % 6);
								if (beforeCorma != null && beforeCorma.equals(mine.point)) {
									ship.mineCd = MINE_CD;
									List<Ship> ships = (ship.team == Team.ME) ? myShips : enemyShips;
									for (Ship foundShip : ships) {
										if (foundShip.id == ship.id) {
											foundShip.mineCd = MINE_CD;
											if (foundShip != ship) {
												--foundShip.mineCd;
											}
											break;
										}
									}
									break;
								}
							}
						}
						mine.point.mined = true;
						break;
					case "CANNONBALL":
						if (arg2 == 0) {
							Point pt = Point.GC[x][y];
							pt.mined = false;
							for (Iterator<Mine> iterator = existMines.iterator(); iterator.hasNext(); ) {
								if (iterator.next().point == pt) {
									iterator.remove();
									break;
								}
							}
							break;
						}
						boolean exist = false;
						for (Ball ball : balls) {
							if (entityId == ball.id) {
								exist = true;
								break;
							}
						}
						if (!exist) {
							Ball tmp = new Ball(entityId, x, y, arg1, arg2);
							balls.add(tmp);
							tmp.point.addShoot(tmp);
						}
						break;
				}
			}
			for (Mine mine : existMines) {
				if (mines.contains(mine)) {
					continue;
				}
				boolean visible = false;
				for (Ship ship : myShips) {
					if (ship.point.hypot(mine.point) <= MINE_VISIBILITY_RANGE) {
						visible = true;
						break;
					}
				}
				if (visible) {
					mine.point.mined = false;
				} else {
					boolean removed = false;
					for (Ship currShip : myShips) {
						if (currShip.head.equals(mine.point) || currShip.point.equals(mine.point) || currShip.back.equals(mine.point)) {
							removed = true;
							mine.point.mined = false;
							break;
						}
					}
					if (removed) continue;
					for (Ship currShip : enemyShips) {
						if (currShip.head.equals(mine.point) || currShip.point.equals(mine.point) || currShip.back.equals(mine.point)) {
							removed = true;
							mine.point.mined = false;
							break;
						}
					}
					if (!removed) mines.add(mine);
				}
			}
			for (Ship ship : myShips) {
				prevStep[ship.id] = ship;
			}
			for (Ship ship : enemyShips) {
				prevStep[ship.id] = ship;
			}
			allShips.clear();
			allShips.addAll(myShips);
			allShips.addAll(enemyShips);
		}

		//		List<DebugType> enabledDebugs = Arrays.asList(DebugType.INPUT, DebugType.FATAL);
		List<DebugType> enabledDebugs = Arrays.asList(DebugType.PROCESSING_TIME, DebugType.SELF_DESTRUCT, DebugType.SHOOTING, DebugType.FATAL);

		void debug(Object str, DebugType debugType) {
			if (enabledDebugs.contains(debugType)) {
				if (debugType == DebugType.FATAL) {
					for (int i = 0; i != 10; ++i) {
						System.err.println("#####################################" + str);
					}
				} else {
					System.err.println(str);
				}
			}
		}
	}

	private enum DebugType {
		INPUT, PROCESSING_TIME, FATAL, SHOOTING, SELF_DESTRUCT
	}

	private static class Entity {
		int id;
		Point point;

		public Entity(int id, Point point) {
			this.point = point;
			this.id = id;
		}

		public Entity(int id, int x, int y) {
			this.id = id;
			point = Point.GC[x][y];
		}
	}

	private static class Barrel extends Entity {
		int rumCount;

		public Barrel(int id, Point point, int rumCount) {
			super(id, point);
			this.rumCount = rumCount;
		}

		public Barrel(int id, int x, int y, int rumCount) {
			super(id, x, y);
			this.rumCount = rumCount;
		}
	}

	private static class Ball extends Entity {
		int stepsToHit;
		int shooterEntityId;

		public Ball(int id, Point pt, int shooterEntityId, int stepsToHit) {
			super(id, pt);
			this.shooterEntityId = shooterEntityId;
			this.stepsToHit = stepsToHit;
		}

		public Ball(int id, int x, int y, int shooterEntityId, int stepsToHit) {
			super(id, x, y);
			this.shooterEntityId = shooterEntityId;
			this.stepsToHit = stepsToHit;
		}
	}

	private static class Mine extends Entity {
		public Mine(int id, int x, int y) {
			super(id, x, y);
		}

		@Override
		public boolean equals(Object o) {
			return id == ((Entity) o).id;
		}
	}

	private static class Ship extends Entity {
		int orientation;
		int speed;
		int rumCount;
		Team team;

		Point head;
		Point back;
		Point preBack;
		int stuckCnt;
		LinkedList<SimulationInfo> simulationInfos = new LinkedList<>();
		ArrayList<ActionType> actions = new ArrayList<>();
		int shootCd;
		int mineCd;

		public Ship(int id, int x, int y, int orientation, int speed, int rumCount, int team) {
			super(id, x, y);
			this.orientation = orientation;
			this.speed = speed;
			this.rumCount = rumCount;
			this.team = Team.fromInt(team);

			head = point.getNeighbour(orientation);
			back = point.getNeighbour((orientation + 3) % 6);
			shootCd = 0;
		}


		public void updateShip(int x, int y, int orientation, int speed, int rumCount, int team) {
			this.point = Point.GC[x][y];
			this.orientation = orientation;
			this.speed = speed;
			this.rumCount = rumCount;
			this.team = Team.fromInt(team);

			head = point.getNeighbour(orientation);
			back = point.getNeighbour((orientation + 3) % 6);
			--mineCd;
			--shootCd;
			actions.clear();
		}

		//for pseudo ship only
		public void partialUpdateShip(Point point, int orientation) {
			this.point = point;
			this.orientation = orientation;
			head = point.getNeighbour(orientation);
			back = point.getNeighbour((orientation + 3) % 6);
		}

		void heal(int amount) {
			this.rumCount = Math.min(100, this.rumCount + amount);
		}

		void damage(int amount) {
			this.rumCount = Math.max(0, this.rumCount - amount);
		}

		boolean canChoot() {
			return shootCd <= 0;
		}

		boolean canPlaceMine() {
			if (mineCd >= 1 || back.blocked) {
				return false;
			}
			preBack = back.getNeighbour((orientation + 3) % 6);
			if (preBack.blocked || preBack.barrel != null || preBack.mined) {
				return false;
			}
			for (Ship ship : Solution.allShips) {
				if (ship.head == preBack || ship.point == preBack || ship.back == preBack) {
					return false;
				}
			}
			return true;
		}

		public boolean isMyShip() {
			return team == Team.ME;
		}

		public void updateStuckCnt(Ship prev) {
			if (this.point.equals(prev.point) && this.orientation == prev.orientation) {
				this.stuckCnt = prev.stuckCnt + 1;
				System.err.println(String.format("ship %d stucked during %d steps", prev.id, this.stuckCnt));
			} else {
				this.stuckCnt = 0;
			}
		}

		public Ship clone() {
			Ship cloned = new Ship(id, point.x, point.y, orientation, speed, rumCount, team.getInt());
			cloned.mineCd = mineCd;
			cloned.shootCd = shootCd;
			return cloned;
		}

		void storeSimulationInfo() {
			this.simulationInfos.add(new SimulationInfo(this));
		}

		void restoreLastSimulationInfo() {
			this.simulationInfos.pollLast().restore(this);
		}

		void moveFwd() {
			if (head.blocked) {
				speed = 0;
				return;
			}
			back = point;
			point = head;
			head = head.getNeighbour(orientation);
		}

		void moveBwd() {
			point = back;
			head = point;
			back = back.getNeighbour((orientation + 3) % 6);
		}

		void turnLeft() {
			orientation = (orientation + 1) % 6;
			head = point.getNeighbour(orientation);
			back = point.getNeighbour((orientation + 3) % 6);
		}

		void turnRight() {
			orientation = (orientation + 5) % 6;
			head = point.getNeighbour(orientation);
			back = point.getNeighbour((orientation + 3) % 6);
		}

		static class SimulationInfo {
			Point head;
			Point point;
			Point back;
			int orientation;
			int speed;
			int rumCount;

			SimulationInfo(Ship ship) {
				this.head = ship.head;
				this.point = ship.point;
				this.back = ship.back;
				this.orientation = ship.orientation;
				this.speed = ship.speed;
				this.rumCount = ship.rumCount;
			}

			void restore(Ship ship) {
				ship.head = this.head;
				ship.point = this.point;
				ship.back = this.back;
				ship.orientation = this.orientation;
				ship.speed = this.speed;
				ship.rumCount = this.rumCount;
			}
		}
	}

	static class WayCalc {
		int steps;
		int stepsEnemy;
		ActionType nextAction;
		WayCalc prevStep;
		Barrel barrel;

		final Point position;
		final int speed;
		final int orientation;

		public WayCalc(int x, int y, int speed, int orientation) {
			this.steps = -1;
			position = Point.GC[x][y];
			this.speed = speed;
			this.orientation = orientation;
		}

		static WayCalc[][][][] q = new WayCalc[FIELD_WIDTH + 2][FIELD_HEIGHT + 2][6][3];

		static WayCalc[][] getWayCalcs(Point point) {
			return q[point.x][point.y];
		}

		static WayCalc getWayCalc(Ship ship) {
			return q[ship.point.x][ship.point.y][ship.orientation][ship.speed];
		}

		static WayCalc getWayCalc(Ship.SimulationInfo ship) {
			return q[ship.point.x][ship.point.y][ship.orientation][ship.speed];
		}

		static {
			for (int i = 1; i != FIELD_WIDTH + 1; ++i) {
				for (int j = 1; j != FIELD_HEIGHT + 1; ++j) {
					for (int k = 0; k != 6; ++k) {
						for (int l = 0; l != 3; ++l) {
							q[i][j][k][l] = new WayCalc(i, j, l, k);
						}
					}
				}
			}
		}

		static void cleanAll() {
			for (int i = 1; i != FIELD_WIDTH + 1; ++i) {
				for (int j = 1; j != FIELD_HEIGHT + 1; ++j) {
					for (int k = 0; k != 6; ++k) {
						for (int l = 0; l != 3; ++l) {
							q[i][j][k][l].clear();
						}
					}
				}
			}
		}

		void clear() {
			this.steps = -1;
			this.stepsEnemy = -1;
			this.barrel = null;
			this.position.possibleMinedStep = 100;
		}

		public String toShortString() {
			return "WayCalc{" +
					"steps=" + steps +
					",\n nextAction=" + nextAction +
					",\n barrelId=" + (barrel == null ? 0 : barrel.id) +
					",\n position=" + position +
					",\n speed=" + speed +
					",\n orientation=" + orientation +
					'}';
		}

		@Override
		public String toString() {
			return "WayCalc{" +
					"steps=" + steps +
					",\n nextAction=" + nextAction +
					",\n barrelId=" + (barrel == null ? 0 : barrel.id) +
					",\n position=" + position +
					",\n speed=" + speed +
					",\n orientation=" + orientation +
					",\n prevStep=" + prevStep.toShortString() +
					'}';
		}
	}

	static class Point {
		int x;
		int y;

		boolean blocked;
		boolean mined = false;
		int possibleMinedStep = 100;
		LinkedList<Ball> shoots = new LinkedList<>();
		Barrel barrel;

		int pointScore;
		int tmpScore;

		int q;
		int r;

		static Point[][] GC = new Point[FIELD_WIDTH + 2][FIELD_HEIGHT + 2];
		static Point[][] AC = new Point[36][FIELD_HEIGHT + 2];

		static {
			for (int i = 0; i != FIELD_WIDTH + 2; ++i) {
				for (int j = 0; j != FIELD_HEIGHT + 2; ++j) {
					Point pt = new Point(i, j);
					GC[i][j] = pt;
					AC[pt.q][pt.r] = pt;
				}
			}
			for (int i = 0; i != FIELD_WIDTH + 2; ++i) {
				GC[i][0].blocked = true;
				GC[i][22].blocked = true;
			}
			for (int j = 0; j != FIELD_HEIGHT + 2; ++j) {
				GC[0][j].blocked = true;
				GC[24][j].blocked = true;
			}
		}

		Point(int x, int y) {
			this.x = x;
			this.y = y;

			this.q = x - (y + (y & 1)) / 2 + 11;
			this.r = y;
		}

		public int hypot(Point o) {
			int t = q - o.q;
			int t2 = r - o.r;
			return (Math.abs(t) + Math.abs(t + t2) + Math.abs(t2)) / 2;
		}

		public Point getNeighbour(int orientation) {
			switch (orientation) {
				case 0:
					return getPt(q + 1, r);
				case 1:
					return getPt(q + 1, r - 1);
				case 2:
					return getPt(q, r - 1);
				case 3:
					return getPt(q - 1, r);
				case 4:
					return getPt(q - 1, r + 1);
				case 5:
					return getPt(q, r + 1);
			}
			return null;
		}

		Point getPt(int q, int r) {
			if (q < 0 || q >= 35) { // AC.length
				return null;
			}
			if (r < 0 || r >= 23) { // AC[q].length
				return null;
			}
			return AC[q][r];
		}

		public boolean cellOfDamage() {
			return mined || !shoots.isEmpty() && shoots.peekFirst().stepsToHit < 2;
		}

		void addShoot(Ball ball) {
			ListIterator<Ball> ballListIterator = shoots.listIterator();
			while (ballListIterator.hasNext()) {
				Ball tmp = ballListIterator.next();
				if (tmp.id == ball.id) {
					return;
				}
				if (tmp.stepsToHit > ball.stepsToHit) {
					ballListIterator.add(ball);
					return;
				}
			}
			shoots.addLast(ball);
		}

		void removeBall(int ballId) {
			ListIterator<Ball> ballListIterator = shoots.listIterator();
			while (ballListIterator.hasNext()) {
				if (ballListIterator.next().id == ballId) {
					ballListIterator.remove();
					return;
				}
			}
		}

		void putPossibleMine(int step) {
			this.possibleMinedStep = Math.min(this.possibleMinedStep, step);
		}

		@Override
		public String toString() {
			return (x - 1) + " " + (y - 1);
		}

		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;

			Point point = (Point) o;

			return x == point.x && y == point.y;
		}
	}


	enum Team {
		ME, ENEMY;

		static Team fromInt(int team) {
			return team == 1 ? ME : ENEMY;
		}

		int getInt() {
			return this == ME ? 1 : 0;
		}
	}

	static class ShootMineActions {
		List<ActionType> mineActione = new ArrayList<>();
		List<Point> mineMarkeredPoints = new ArrayList<>();
		List<ActionType> shootActions = new ArrayList<>();
		List<Point> shootMarkeredPoints = new ArrayList<>();
		List<Point> markeredPoints = new ArrayList<>();
		LinkedList<Ship.SimulationInfo> simulationInfo = new LinkedList<>();
		Ship.SimulationInfo nextStep;

		void updateSimulationInfo(List<Ship.SimulationInfo> simulationInfos) {
			simulationInfo.clear();
			simulationInfo.addAll(simulationInfos);
		}

		void updateMine(List<ActionType> actionTypes, ArrayDeque<Point> markeredPoints) {
			this.mineActione.clear();
			this.mineActione.addAll(actionTypes);
			this.mineMarkeredPoints.clear();
			this.mineMarkeredPoints.addAll(markeredPoints);
		}

		void updateShoot(List<ActionType> actionTypes, ArrayDeque<Point> markeredPoints) {
			this.shootActions.clear();
			this.shootActions.addAll(actionTypes);
			this.shootMarkeredPoints.clear();
			this.shootMarkeredPoints.addAll(markeredPoints);
		}

		void applyMine() {
			markeredPoints.clear();
			markeredPoints.addAll(mineMarkeredPoints);
		}

		void applyShoot() {
			markeredPoints.clear();
			markeredPoints.addAll(shootMarkeredPoints);
		}
	}

	enum ActionType {
		PORT, // left
		STARBOARD, // right
		FASTER, SLOWER, WAIT
	}
}