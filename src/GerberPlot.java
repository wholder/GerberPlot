import javax.swing.*;
import javax.swing.filechooser.FileNameExtensionFilter;
import java.awt.*;
import java.awt.font.GlyphVector;
import java.awt.font.TextAttribute;
import java.awt.geom.*;
import java.awt.image.BufferedImage;
import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.*;
import java.util.List;
import java.util.prefs.Preferences;

/**
 * This code began as rewrite of the "Plotter" portion of Philipp Knirsch's "Gerber RS-274D/X file viewer in Java"
 * (see: http://www.wizards.de/phil/java/rs274x.html) but, the current code has been extensively rewritten and
 * expanded to use Java's Shape-based graphics and fix numerous small issues I found with the original code.  I've
 * also  added more features from the 2017.5 Gerber Format Specification by Ucamco, such as partial support for
 * "AD"-type Macros and implemented many of the Aperture primitives needed for this, although some of the Aperture
 * primitives remain untested, as I've yet to find a Gerber design that uses them. The untested code is noted in the
 * source for the flashAperture() method.
 *
 * Internally, the code first converts the Gerber file into a list of shapes in "drawItems".  Then, if renderMode is
 * set to DRAW_IMAGE (the default when started), it draws this list of shapes directly to the screen.  However, if
 * renderMode is set to RENDER_FILLED or RENDER_OUTLINE, getBoardArea() is called to compute an Area shape by using
 * the 2D constructive geometry operations add() and subtract().  This converts all the individual shapes in drawItems
 * into a single Shape the contains all the geometry of the PCB design.  Unfortunately, computing this Area becomes
 * exponentially inefficient with larger Gerber files because, as each new shape is added, or subtracted its takes
 * increasinglt more time to calculate all the intersections.  So, a progress bar is displayed to show the progress of
 * the calculation.  Once the Area is computed, however, it can be resized and redrawn much more quickly than when
 * renderMode == DRAW_IMAGE.
 *
 * I've tried to adhere as close as possible to the latest revision of the Ucamco spec, version, 2017.05, which means
 * my code may not parse some older Gerber files, such as ones that reply on on undocumented behavior, or deprecated
 * operations.  In particular, G36/G37 regions specified like this:
 *
 *    G36*G01X-0001Y-0001D02*X1076D01*Y0226*X-0001*Y-0001*G37*
 *
 * Will not render because all of the coordinate values need to be followed by a D01 operation to render, such as:
 *
 *    G36*G01X-0001Y-0001D02*X1076D01*Y0226D01*X-0001D01*Y-0001D01*G37*
 *
 * Note: derived from GerberPlotArea3 in GerberTools Project
 */

class GerberPlot extends JPanel implements Runnable {
  private static final double   SCREEN_PPI = Toolkit.getDefaultToolkit().getScreenResolution();
  // Colors used to Render elements of the PCB design
  private static final Color    COPPER = new Color(0xB87333);
  private static final Color    BOARD = Color.white;
  private static final Color    OUTLINE = Color.black;
  // Aperture types
  private static final int      CIRCLE = 1;
  private static final int      RECTANGLE = 2;
  private static final int      OBROUND = 3;
  private static final int      POLYGON = 4;
  // Aperture Macro Primitive Types
  private static final int      PRIM_CIRCLE = 10;
  private static final int      PRIM_VLINE = 11;
  private static final int      PRIM_CLINE = 12;
  private static final int      PRIM_OUTLINE = 13;
  private static final int      PRIM_POLYGON = 14;
  private static final int      PRIM_MOIRE = 15;
  private static final int      PRIM_THERMAL = 16;
  // Interpolation modes
  private static final int      LINEAR = 0;
  private static final int      CLOCK = 1;
  private static final int      CCLOCK = 2;
  // Draw and Render Modes
  private static final int      DRAW_IMAGE = 1;
  private static final int      RENDER_FILLED = 2;
  private static final int      RENDER_OUTLINE = 3;
  // Internal scaling parameters
  private static final double   renderScale = 10;   // scales up Shapes to improve render
  private static final int      pixelGap = 2;       // Adds border around dsplayed image
  // State machine variables
  private List<String> cmdList;     // List containing all single commands and tokens
  private int cmdIdx;               // Current position in cmdList for parser
  private boolean extCmd;           // True when processing an extended command
  private double curX;              // Current X position
  private double curY;              // Current Y position
  private double arcX;              // X center of arc
  private double arcY;              // Y center of arc
  private int interpol = LINEAR;    // Current interpolation mode
  private boolean inRegion;         // Flag for Path2D-based region active
  private boolean multi;            // Flag for single or multiquadrant interpolation
  private boolean stop;             // Stop program flag
  private boolean millimeters;      // If true, all coordinates are in millimeters, else inches
  private Path2D.Double path;       // Polygon of the area to be filled
  private boolean pathStarted;
  // State machine variables for the extended commands
  private boolean omitLeadZeros;    // Omit leading zeros, else omit trailing zeroes
  private int xSgnf = 2;            // Number of digits of X-axis before decimal
  private int xFrac = 3;            // Number of digits of X-axis after decimal
  private int ySgnf = 2;            // Number of digits of Y-axis before decimal
  private int yFrac = 3;            // Number of digits of Y-axis after decimal
  // Aperture lookup Map and working variable
  private Map<String,Macro> macroMap;
  private Map<Integer,List<Aperture>> aperturesMap;
  private List<Aperture>  apertures;
  // PCB shape and control flags
  private boolean isDark = true;    // True if drawing copper
  private Area board;
  private Rectangle.Double bounds;
  private List<DrawItem> drawItems;
  private int renderMode = DRAW_IMAGE;
  private boolean built;
  private boolean rendered;
  private boolean running;
  private static JFrame frame;
  private int lastDone;
  private JMenu fileMenu, optMenu;

  private Preferences prefs = Preferences.userRoot().node(this.getClass().getName());

  static class DrawItem {
    boolean   drawCopper;
    Shape     shape;

    DrawItem (Shape shape, boolean drawCopper) {
      this.shape = shape;
      this.drawCopper = drawCopper;
    }
  }

  static class Macro {
    List<String>  cmds = new LinkedList<>();

    void addCmd (String cmd) {
      cmds.add(cmd);
    }
  }

  static class Aperture {
    int           type;
    List<Double>  parms = new LinkedList<>();

    Aperture (int type) {
      this.type = type;
    }

    void addParm (double parm) {
      parms.add(parm);
    }
  }

  private void resetStateMachine () {
    bounds = new Rectangle.Double();
    drawItems = new ArrayList<>();
    apertures = new LinkedList<>();
    macroMap = new HashMap<>();
    aperturesMap = new HashMap<>();
    omitLeadZeros = true;
    path = new Path2D.Double();
    pathStarted = false;
    curX = 0.0;
    curY = 0.0;
    interpol = LINEAR;
    inRegion = false;
    multi = false;
    stop = false;
    omitLeadZeros = true;
    millimeters = false;
    xSgnf = 2;
    xFrac = 3;
    ySgnf = 2;
    yFrac = 3;
    cmdIdx = 0;
    extCmd = false;
    lastDone = 0;
  }

  private GerberPlot (JFrame frame) {
    frame.setTitle(this.getClass().getSimpleName());
    JMenuBar menuBar = new JMenuBar();
    // Add "File" Menu
    fileMenu = new JMenu("File");
    // Add "Open" Item to File Menu
    JMenuItem loadGbr = new JMenuItem("Open Gerber File");
    loadGbr.addActionListener(ev -> {
      JFileChooser fileChooser = new JFileChooser();
      fileChooser.setDialogTitle("Select a Gerber File");
      fileChooser.setDialogType(JFileChooser.OPEN_DIALOG);
      FileNameExtensionFilter nameFilter = new FileNameExtensionFilter("Gerber files (*.gbr)", "gbr");
      fileChooser.addChoosableFileFilter(nameFilter);
      fileChooser.setFileFilter(nameFilter);
      fileChooser.setSelectedFile(new File(prefs.get("default.dir", "/")));
      if (fileChooser.showOpenDialog(this) == JFileChooser.APPROVE_OPTION) {
        try {
          File tFile = fileChooser.getSelectedFile();
          prefs.put("default.dir", tFile.getAbsolutePath());
          frame.setTitle(this.getClass().getSimpleName() + " - " + tFile.toString());
          built = false;
          rendered = false;
          // Read file and strip out line delimiters
          StringBuilder buf = new StringBuilder();
          BufferedReader br = new BufferedReader(new FileReader(tFile));
          String line;
          while ((line = br.readLine()) != null) {
            buf.append(line);
          }
          br.close();
          cmdList = new ArrayList<>();
          StringTokenizer st = new StringTokenizer(buf.toString(), "%*", true);
          int pos = 0;
          while (st.hasMoreTokens()) {
            String token = st.nextToken();
            if (!token.equals("*")) {
              cmdList.add(pos++, token);
            }
          }
          (new Thread(this)).start();
        } catch (Exception ex) {
          JOptionPane.showMessageDialog(this, "Unable to load file", "Error", JOptionPane.PLAIN_MESSAGE);
          ex.printStackTrace(System.out);
        }
      }
    });
    fileMenu.add(loadGbr);
    menuBar.add(fileMenu);
    // Add "Options" Menu
    setBackground(BOARD);
    optMenu = new JMenu("Options");
    ButtonGroup group = new ButtonGroup();
    menuBar.add(optMenu);
    JRadioButtonMenuItem mItem;
    optMenu.add(mItem = new JRadioButtonMenuItem("Draw Direct", true));
    group.add(mItem);
    mItem.addActionListener(e -> setDisplayMode(DRAW_IMAGE));
    optMenu.add(mItem = new JRadioButtonMenuItem("Render Filled"));
    group.add(mItem);
    mItem.addActionListener(e -> setDisplayMode(RENDER_FILLED));
    optMenu.add(mItem = new JRadioButtonMenuItem("Render Outline"));
    group.add(mItem);
    mItem.addActionListener(e -> setDisplayMode(RENDER_OUTLINE));
    frame.setJMenuBar(menuBar);
  }

  public static void main (String[] argv) throws IOException {
    frame = new JFrame();
    frame.setLocation(50, 50);
    GerberPlot panel = new GerberPlot(frame);
    panel.setPreferredSize(new Dimension(600, 400));
    frame.add("Center", panel);
    frame.pack();
    frame.setVisible(true);
    frame.setDefaultCloseOperation(WindowConstants.EXIT_ON_CLOSE);
  }

  public void paint (Graphics g) {
    Graphics2D g2 = (Graphics2D) g;
    g2.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
    Dimension size = getSize();
    Image bufImg = new BufferedImage(size.width, size.height, BufferedImage.TYPE_4BYTE_ABGR);
    Graphics2D offScr = (Graphics2D) bufImg.getGraphics();
    offScr.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
    if (built) {
      if (renderMode == DRAW_IMAGE) {
        double scaleX = (size.width - pixelGap * 2) / bounds.width;
        double scaleY = (size.height - pixelGap * 2) / bounds.height;
        double scale = Math.min(scaleX, scaleY);
        offScr.drawImage(getBoardImage(scale), null, 0, 0);
      } else {
        if (board != null) {
          double scaleX = (size.width - pixelGap * 2) / bounds.width;
          double scaleY = (size.height - pixelGap * 2) / bounds.height;
          double scale = Math.min(scaleX, scaleY);
          offScr.setColor(BOARD);
          offScr.fillRect(0, 0, size.width, size.height);
          offScr.scale(scale, scale);
          offScr.translate(pixelGap / scale, pixelGap / scale);
          if (renderMode == RENDER_FILLED) {
            offScr.setColor(COPPER);     // Copper color
            offScr.fill(board);
          } else {
            offScr.setColor(OUTLINE);
            offScr.setStroke(new BasicStroke(0.5f / (float) scale));
            offScr.draw(board);
          }
        } else {
          // Draw progress bar during rendering step
          float ratio = lastDone / 100f;
          Rectangle2D bar = new Rectangle2D.Float(40, size.height / 2 - 10, size.width * ratio - 80, 20);
          offScr.setColor(Color.blue);
          offScr.fill(bar);
          Rectangle2D frm = new Rectangle2D.Float(40, size.height / 2 - 10, size.width - 80, 20);
          offScr.setColor(Color.gray);
          offScr.setStroke(new BasicStroke(3.0f));
          offScr.draw(frm);
        }
      }
    } else {
      String text = this.getClass().getSimpleName();
      Font font = new Font("OCR A Std", Font.PLAIN, 80);
      HashMap<TextAttribute, Object> attrs = new HashMap<>();
      attrs.put(TextAttribute.KERNING, TextAttribute.KERNING_ON);
      attrs.put(TextAttribute.LIGATURES, TextAttribute.LIGATURES_ON);
      attrs.put(TextAttribute.TRACKING, -0.15);
      font = font.deriveFont(attrs);
      GlyphVector gv = font.createGlyphVector(g2.getFontRenderContext(), text);
      Rectangle2D bnds = gv.getVisualBounds();
      AffineTransform at = new AffineTransform();
      double xOff = (size.width - bnds.getWidth()) / 2;
      double yOff = (size.height - bnds.getHeight()) / 2;
      at.translate(-bnds.getX() + xOff, -bnds.getY() + yOff);
      g2.setColor(Color.lightGray);
      g2.fill(at.createTransformedShape(gv.getOutline()));
      at.translate(-3, -3);
      g2.setColor(COPPER);
      g2.fill(at.createTransformedShape(gv.getOutline()));

    }
    offScr.dispose();
    g2.drawImage(bufImg, 0, 0, this);
  }

  private void setDisplayMode (int mode) {
    renderMode = mode;
    (new Thread(this)).start();
  }

  public void run () {
    if (!running) {
      fileMenu.setEnabled(false);
      optMenu.setEnabled(false);
      running = true;
      if (!built) {
        resetStateMachine();
        while (cmdIdx < cmdList.size() && !stop) {
          String cmd = cmdList.get(cmdIdx);
          // If we entered or exited an extended command, switch the flag
          if (cmd.equals("%")) {
            extCmd = !extCmd;
            cmdIdx++;
            continue;
          }
          if (extCmd) {
            // Handle extended RS-274X command
            if (!doExtendedCmd()) {
              System.out.println("Error: Failed executing command: " + cmd);
              return;
            }
          } else {
            // Handle standard command
            if (!doNormalCmd()) {
              System.out.println("Error: Failed executing command: " + cmd);
              return;
            }
          }
        }
        // Set JPanel dimensions to display board at 5x scale
        double scaleFactor = SCREEN_PPI / (renderScale / 1);
        Dimension size = new Dimension((int) (bounds.width * scaleFactor) + pixelGap * 2, (int) (bounds.height * scaleFactor) + pixelGap * 2);
        setPreferredSize(size);
        frame.pack();
        built = true;
      }
      if (!rendered && (renderMode == RENDER_FILLED || renderMode == RENDER_OUTLINE)) {
        board = getBoardArea();
        // Invert Y axis to match Java Graphics's upper-left origin
        AffineTransform at = new AffineTransform();
        at.scale(1, -1);
        at.translate(-bounds.x, -bounds.height);
        board = new Area(at.createTransformedShape(board));
        rendered = true;
      }
      repaint();
      fileMenu.setEnabled(true);
      optMenu.setEnabled(true);
      running = false;
    }
  }

  private void updateProgress (int idx) {
    int done = Math.round((float) idx / drawItems.size() * 100f);
    if (done != lastDone) {
      lastDone = done;
      repaint();
    }
  }

  private BufferedImage getBoardImage (double scale) {
    double scaleFactor = SCREEN_PPI / (renderScale / scale);
    Dimension size = new Dimension((int) (bounds.width * scaleFactor) + pixelGap * 2, (int) (bounds.height * scaleFactor) + pixelGap * 2);
    BufferedImage bufImg = new BufferedImage(size.width, size.height, BufferedImage.TYPE_4BYTE_ABGR);
    Graphics2D offScr = (Graphics2D) bufImg.getGraphics();
    offScr.setRenderingHint(RenderingHints.KEY_ANTIALIASING, RenderingHints.VALUE_ANTIALIAS_ON);
    offScr.setColor(BOARD);
    offScr.fillRect(0, 0, size.width, size.height);
    offScr.scale(scale, scale);
    offScr.translate(pixelGap / scale, pixelGap / scale);
    for (DrawItem item : drawItems) {
      // Invert Y axis to match Java Graphics's upper-left origin
      AffineTransform at = new AffineTransform();
      at.scale(1, -1);
      at.translate(-bounds.x, -bounds.height);
      Shape shape = at.createTransformedShape(item.shape);
      offScr.setColor(item.drawCopper ? COPPER : BOARD);
      offScr.fill(shape);
    }
    offScr.dispose();
    return bufImg;
  }

  private Area getBoardArea () {
    Area pcb = new Area();
    int count = 0;
    for (DrawItem item : drawItems) {
      if (item.drawCopper) {
        pcb.add(new Area(item.shape));
      } else {
        pcb.subtract(new Area(item.shape));
      }
      updateProgress(++count);
    }
    return pcb;
  }

  private void addToBoard (Shape shape, boolean drawCopper) {
    bounds.add(shape.getBounds2D());
    drawItems.add(new DrawItem(shape, drawCopper));
  }

  // Scale X coordinates (to improve Shape precision)
  private double dX (double xx) {
    return xx * renderScale;
  }

  // Used to scale Y coordinates
  private double dY (double yy) {
    return yy * renderScale;
  }

  // Used to scale width values
  private double dW (double xx) {
    return xx * renderScale;
  }

  // Used to scale height values
  private double dH (double yy) {
    return yy * renderScale;
  }

  //
  // Search for the end of a number and returns the length up to the last
  // character. The format of a number looks like this:
  //
  //   [+|-]xxx[.yyy]
  //
  // TODO: rework this logic to simplify and meet spec
  //
  private int numberEndIndex (String cmd, int pstart) {
    int p;
    for (p = pstart; p < cmd.length(); p++) {
      char cc = cmd.charAt(p);
      if (!Character.isDigit(cc)  && cc != '-' && cc != '+' && cc != '.')
        break;
    }
    return p;
  }

  /**
   * Takes a numeric string representing a floating point value with no decimal point and
   * use the values signif and frac (which represent the number of left side and right side
   * digits, respectively), to convert input to a double value.  If "omitLeadZeros" is true
   * then use total of signif and frac vs length of string to figure out how many leading
   * zeros were omitted.
   * Note: also handles deprecated "omit trailing zero" case when omitLeadZeros == false
   * @param num numeric string without a decimal point
   * @param signif number of integral (left side) digits expected
   * @param frac number of fractional (right side) digits expected
   * @return double value for input string
   */
  private double normalize (String num, int signif, int frac) {
    double dVal = Double.parseDouble(num);
    if (!omitLeadZeros) {
      dVal *= Math.pow(10, (signif + frac - num.length()));
    }
    dVal /= Math.pow(10, frac);
    return millimeters ? dVal / 25.4 : dVal;
  }

  //
  // Handles an extended RS-274X command. They always start with a 2
  // character specifier, followed by various parameters, sometimes even
  // more commands.
  //
  private boolean doExtendedCmd () {
    while (cmdIdx < cmdList.size()) {
      String cmd = cmdList.get(cmdIdx);
      // End of eXtended command, so return true.
      if (cmd.equals("%")) {
        return true;
      }
      //System.out.println(cmd);
      // Process command and any subcommands
      switch (cmd.substring(0, 2)) {
        case "AD":
          // Aperture definition
          Aperture app = null;
          int nl = numberEndIndex(cmd, 3);
          int pd = Integer.parseInt(cmd.substring(3, nl));
          int te = cmd.indexOf(',', nl);
          String type = cmd.substring(nl, te);
          cmd = cmd.substring(te + 1);
          List<Aperture> aList = new LinkedList<>();
          aperturesMap.put(pd, aList);
          if (type.length() > 1) {
            // Process one, or more Aperture primitives defined in a Macro
            List<Double> aParms = new ArrayList<>();
            StringTokenizer st = new StringTokenizer(cmd, "X");
            while (st.hasMoreTokens()) {
              aParms.add(Double.parseDouble(st.nextToken()));
            }
            Macro macro = macroMap.get(type);
            for (String mCmd : macro.cmds) {
              if (mCmd.startsWith("0 ")) {
                // Skip over a comment within the macro  (4.5.4.1)
                // System.out.println("Comment: " + mCmd.substring(2));
              } else if (mCmd.startsWith("$")) {
                // Skip over processing an equation within the macro, but log it for future work
                System.out.println("Equation: " + mCmd.substring(1));
              } else {
                // Process one of the primitives defined in the Macro
                String[] mParms = mCmd.split(",");
                int primType = Integer.parseInt(mParms[0]);
                switch (primType) {
                  case 1:               // Circle Primitive (4.5.4.2)
                    app = new Aperture(PRIM_CIRCLE);
                    break;
                  case 4:               // Outline Primitive  (4.5.4.5)
                    app = new Aperture(PRIM_OUTLINE);
                    break;
                  case 5:               // Polygon Primitive  (4.5.4.6)
                    app = new Aperture(PRIM_POLYGON);
                    break;
                  case 6:               // Moire Primitive  (4.5.4.7)
                    app = new Aperture(PRIM_MOIRE);
                    break;
                  case 7:               // Thermal Primitive  (4.5.4.8)
                    app = new Aperture(PRIM_THERMAL);
                    break;
                  case 20:              // Vector Line Primitive (4.5.4.3)
                    app = new Aperture(PRIM_VLINE);
                    break;
                  case 21:              // Center Line Primitive (4.5.4.4)
                    app = new Aperture(PRIM_CLINE);
                    break;
                }
                if (app != null) {
                  // Scan for variable in Macro's parms and plug in values from Aperture's parms
                  for (String mParm : mParms) {
                    if (mParm.startsWith("$")) {
                      int idx = Integer.parseInt(mParm.substring(1));
                      app.addParm(aParms.get(idx - 1));
                    } else {
                      app.addParm(Double.parseDouble(mParm));
                    }
                  }
                  aList.add(app);
                }
              }
            }
          } else {
            // Process non-Macro Aperture definition
            switch (type.charAt(0)) {
              case 'C':
                app = new Aperture(CIRCLE);
                break;
              case 'R':
                app = new Aperture(RECTANGLE);
                break;
              case 'O':
                app = new Aperture(OBROUND);
                break;
              case 'P':
                app = new Aperture(POLYGON);
                break;
              default:
                System.out.println("Unknown Aperture type: " + cmd);
                break;
            }
            if (app != null) {
              StringTokenizer st = new StringTokenizer(cmd, "X");
              while (st.hasMoreTokens()) {
                app.addParm(Double.parseDouble(st.nextToken()));
              }
              aList.add(app);
            }
          }
          break;
        case "AM":
          // Aperture Macros
          String name = cmd.substring(2);
          Macro macro = new Macro();
          macroMap.put(name, macro);
          while (cmdIdx + 1 < cmdList.size() && !cmdList.get(cmdIdx + 1).equals("%")) {
            String tmp = cmdList.get(++cmdIdx);
            macro.addCmd(tmp);
          }
          break;
        case "FS":
          // Parse the format statement, such as "FSTAX24Y24"
          omitLeadZeros = cmd.charAt(2) == 'L';
          cmd = cmd.substring(4);
          if (cmd.startsWith("X")) {
            xSgnf = Integer.parseInt(cmd.substring(1, 2));
            xFrac = Integer.parseInt(cmd.substring(2, 3));
            cmd = cmd.substring(3);
          }
          if (cmd.startsWith("Y")) {
            ySgnf = Integer.parseInt(cmd.substring(1, 2));
            yFrac = Integer.parseInt(cmd.substring(2, 3));
          }
          break;
        case "LP":
          isDark = cmd.charAt(2) == 'D';
          break;
        case "MO":      // Set units (inches or millimeters)
          millimeters = cmd.charAt(2) == 'M';
          break;
        case "AS":      // Deprecated command (ignored)
        case "IN":      // Deprecated command (ignored)
        case "IP":      // Deprecated command (ignored)
        case "IR":      // Deprecated command (ignored)
        case "LN":      // Deprecated command (ignored)
        case "MI":      // Deprecated command (ignored)
        case "OF":      // Deprecated command (ignored)
        case "SF":      // Deprecated command (ignored)
          //System.out.println("Deprecated extended command: " + cmd);
          break;
        default:
          System.out.println("Unknown extended command: " + cmd);
          break;
      }
      cmdIdx++;
    }
    return true;
  }

  //
  // Handles a old RS command. They always start with only 1 character and
  // are much less complex and nested as the eXtended commands.
  //
  private boolean doNormalCmd () {
    // Allow reuse of prior coordinates
    double nx = curX;
    double ny = curY;
    while (cmdIdx < cmdList.size()) {
      String cmd = cmdList.get(cmdIdx);
      //System.out.println(cmd);
      // Asterisk denotes end of command
      if (cmd.equals("*")) {
        return true;
      }
      // This check is needed to recover from unanticipated states
      // TODO: investigate further
      if (cmd.equals("%")) {
        return true;
      }
      // Process subcommands
      while (cmd.length() > 0) {
        switch (cmd.charAt(0)) {
          case 'N': {
            // Line number (ignored)
            int p = numberEndIndex(cmd, 1);
            cmd = cmd.substring(p);
          } continue;
          case 'G':
            String code = cmd.substring(1, 3);
            cmd = cmd.substring(3);
            switch (code) {
              case "01":      // G01
                // Switch to linear interpolation with scale 1.0
                interpol = LINEAR;
                continue;
              case "02":    // G02
                // Switch to clockwise interpolation
                interpol = CLOCK;
                continue;
              case "03":    // G03
                // Switch to counter clockwise interpolation
                interpol = CCLOCK;
                continue;
              case "04":    // G04 - Comment
                cmd = "";
                continue;
              case "10":    // G10
                // Switch to linear interpolation with scale 10
                interpol = LINEAR;
                continue;
              case "36":    // G36 - Start new filed area polygon
                inRegion = true;
                path = new Path2D.Double();
                pathStarted = false;
                continue;
              case "37":    // G37 - End area fill
                addToBoard(path, isDark);
                inRegion = false;
                continue;
              case "54":    // G54
              case "55":    // G55
                // Select an aperture, Deprecated
                continue;
              case "74":    // G74
                // Switch to single quadrant (no circular interpolation)
                multi = false;
                continue;
              case "75":    // G75
                // Switch to multi quadrant (circular interpolation)
                multi = true;
                continue;
              default:
                continue;
            }
          case 'X': {                     // Set X position.
            int idx = numberEndIndex(cmd, 1);
            nx = normalize(cmd.substring(1, idx), xSgnf, xFrac);
            cmd = cmd.substring(idx);
          } continue;
          case 'Y': {                     // Set Y position.
            int idx = numberEndIndex(cmd, 1);
            ny = normalize(cmd.substring(1, idx), ySgnf, yFrac);
            cmd = cmd.substring(idx);
          } continue;
          case 'I': {                     // Find the relative X center of the circle
            int idx = numberEndIndex(cmd, 1);
            arcX = normalize(cmd.substring(1, idx), xSgnf, xFrac);
            cmd = cmd.substring(idx);
          } continue;
          case 'J': {                     // Find the relative Y center of the circle
            int idx = numberEndIndex(cmd, 1);
            arcY = normalize(cmd.substring(1, idx), ySgnf, yFrac);
            cmd = cmd.substring(idx);
          } continue;
          case 'D': {                     // Operation code
            //System.out.println("  " + cmd);
            int idx = numberEndIndex(cmd, 1);
            int nd = Integer.parseInt(cmd.substring(1, idx));
            cmd = cmd.substring(idx);
            if (nd >= 10) {               // Select aperture
              apertures = aperturesMap.get(nd);
              if (apertures == null) {
                throw new IllegalStateException("Aperture " + nd + " not found");
              }
            } else if (nd == 1) {         // D01: Interpolate operation
              if (inRegion) {
                if (interpol == LINEAR) {
                  if (pathStarted) {
                    path.lineTo(dX(nx), dY(ny));
                  } else {
                    path.moveTo(dX(nx), dY(ny));
                    pathStarted = true;
                  }
                } else {
                  for (Aperture aper : apertures) {
                    drawArc(aper, nx, ny, false);
                  }
                }
              } else {
                if (interpol == LINEAR) {
                  for (Aperture aper : apertures) {
                    interpolateAperture(aper, curX, curY, nx, ny);
                  }
                } else {
                  for (Aperture aper : apertures) {
                    drawArc(aper, nx, ny, true);
                  }
                }
              }
            } else if (nd == 2) {         // D02: Move operation
              if (inRegion) {
                if (pathStarted) {
                  path.lineTo(dX(nx), dY(ny));
                } else {
                  path.moveTo(dX(nx), dY(ny));
                  pathStarted = true;
                }
              }
            } else if (nd == 3) {         // D03: Flash
              for (Aperture aper : apertures) {
                flashAperture(aper, nx, ny);
              }
            }
          } continue;
          case 'M':
            stop = cmd.startsWith("M00") || cmd.startsWith("M02");
            cmd = "";
            continue;
          default:
            System.out.println("Unrecognized command: " + cmd);
            cmd = "";
        }
      }
      curX = nx;
      curY = ny;
      cmdIdx++;
    }
    return true;
  }

  // This clever bit of code is largely unchanged from the original source except for changes I made
  // to use Java's newer, Shape-based graphics to get more precise, sub pixel-level positioning
  private void drawArc (Aperture app, double nx, double ny, boolean filled) {
    double cx, cy;
    // Calculate the radius first
    double radius = Math.sqrt(Math.pow(arcX, 2) + Math.pow(arcY, 2));
    // Calculate the center of the arc
    if (multi) {
      cx = curX + arcX;
      cy = curY + arcY;
    } else {
      if (interpol == CCLOCK) {
        if (curX < nx)
          cy = curY + arcY;       // Lower half
        else
          cy = curY - arcY;       // Upper half
        if (curY < ny)
          cx = curX - arcX;       // Right half
        else
          cx = curX + arcX;       // Left half
      } else {
        if (curX < nx)
          cy = curY - arcY;       // Upper half
        else
          cy = curY + arcY;       // Lower half
        if (curY < ny)
          cx = curX + arcX;       // Left half
        else
          cx = curX - arcX;       // Right half
      }
    }
    // Calculate angle of starting point, lazy \/    trick here
    double start = 180 * Math.atan((curY - cy) / (curX - cx + .000000001)) / Math.PI;
    if (curX - cx < 0.0) {
      start = 180 + start;        // Left side we have to add 180 degree
    }
    // First calculate angle of the end point
    double arc = 180 * Math.atan((ny - cy) / (nx - cx + .000000001)) / Math.PI;
    if (nx - cx < 0.0) {
      arc = 180 + arc;            // Left side we have to add 180 degree
    }
    // Now lets check if we go clock or counterclockwise
    if (interpol == CCLOCK) {
      arc = arc - start;          // Counterclock, just go from start to end
    } else {
      arc = arc - start - 360;    // Hah, try to figure out this one :)
    }
    // Special case for a full circle.
    if (arc == 0) {
      arc = 360;
    }
    // Calculate the coordinates needed by Arc2D.Double()
    double left   = dX(cx) - dW(radius);
    double upper  = dY(cy) - dW(radius);
    double height = dW(2 * radius);
    double width  = dH(2 * radius);
    if (filled) {
      addToBoard(new Arc2D.Double(left, upper, width, height, start, arc, Arc2D.PIE), isDark);
    } else {
      if (inRegion) {
        Arc2D.Double curve = new Arc2D.Double(left, upper, width, height, start, arc, Arc2D.OPEN);
        path.append(curve.getPathIterator(new AffineTransform()), true);
      } else {
        // TODO: decide if I should handle case where Aperture is a rectangle (see interpolateAperture())
        double diam = dW(app.parms.get(0));
        BasicStroke s1 = new BasicStroke((float) diam, BasicStroke.CAP_ROUND, BasicStroke.JOIN_ROUND);
        addToBoard(s1.createStrokedShape(new Arc2D.Double(left, upper, width, height, start, arc, Arc2D.OPEN)), isDark);
      }
    }
  }

  /**
   * Draw a filled shape specifed by the currrent Aperture object
   * @param x1 x coord of the center of the shape to draw
   * @param y1 y coord of the center of the shape to draw
   */
  private void flashAperture (Aperture app, double x1, double y1) {
    x1 = dX(x1);
    y1 = dY(y1);
    double wid = dW(app.parms.get(0));
    int holeIndex = 0;
    if (app.type == CIRCLE) {
      addToBoard(new Ellipse2D.Double(x1 - wid / 2, y1 - wid / 2, wid, wid), isDark);
      holeIndex = app.parms.size() > 1 ? 1 : 0;
    } else if (app.type == RECTANGLE) {
      double hyt = dH(app.parms.get(1));
      addToBoard(new Rectangle2D.Double(x1 - wid / 2, y1 - hyt / 2, wid, hyt), isDark);
      holeIndex = app.parms.size() > 2 ? 2 : 0;
    } else if (app.type == OBROUND) {
      double hyt = dH(app.parms.get(1));
      double eRadius = Math.min(wid, hyt);
      addToBoard(new RoundRectangle2D.Double(x1 - wid / 2, y1 - hyt / 2, wid, hyt, eRadius, eRadius), isDark);
      holeIndex = app.parms.size() > 2 ? 2 : 0;
    } else  if (app.type == POLYGON) {
      double radius = dW(app.parms.get(0) / 2.0);
      double sides = app.parms.get(1);
      double start = app.parms.get(2);
      Path2D.Double path = new Path2D.Double();
      boolean first = true;
      for (int ii = 0; ii < sides; ii++) {
        double cx = x1 + radius * Math.cos((start + 360 * ii / sides) * Math.PI / 180);
        double cy = y1 + radius * Math.sin((start + 360 * ii / sides) * Math.PI / 180);
        if (first) {
          path.moveTo(cx, cy);
        } else {
          path.lineTo(cx, cy);
        }
        first = false;
      }
      path.closePath();
      addToBoard(path, isDark);
      holeIndex = app.parms.size() > 3 ? 3 : 0;
    } else if (app.type == PRIM_CIRCLE) {
      // Note: coded to spec (4.5.4.2), but untested
      double aDia = dW(app.parms.get(2));
      double aX = dX(app.parms.get(3));
      double aY = dY(app.parms.get(4));
      double rot = app.parms.get(5);  // Rotation pointless for circle, but spec includes it...
      Shape circle = new Ellipse2D.Double(aX - aDia / 2, aY - aDia / 2, aDia, aDia);
      AffineTransform at = new AffineTransform();
      at.translate(x1, y1);
      at.rotate(Math.toRadians(360 - rot));   // Spec says rotation is counterclockwise
      addToBoard(at.createTransformedShape(circle), isDark);
    } else if (app.type == PRIM_CLINE) {
      // Note: tested 11-14-2017 using "BreadboardArduinoZero-30 (U4).osm"
      double aWid = dW(app.parms.get(2));
      double aHyt = dH(app.parms.get(3));
      double aX = dX(app.parms.get(4));
      double aY = dY(app.parms.get(5));
      double rot = app.parms.get(6);
      Shape cline = new Rectangle2D.Double(aX - aWid / 2, aY - aHyt / 2, aWid, aHyt);
      AffineTransform at = new AffineTransform();
      at.translate(x1, y1);
      at.rotate(Math.toRadians(360 - rot));   // Spec says rotation is counterclockwise
      addToBoard(at.createTransformedShape(cline), isDark);
    } else if (app.type == PRIM_OUTLINE) {
      // Note: coded to spec (4.5.4.5) , but untested
      int coords = app.parms.get(2).intValue() + 1; // Includes start point again at end
      Path2D.Double outline = new Path2D.Double();
      for (int ii = 0; ii < coords; ii += 2) {
        if (ii == 0) {
          outline.moveTo(dX(app.parms.get(ii + 3)), dY(app.parms.get(ii + 4)));
        } else {
          outline.lineTo(dX(app.parms.get(ii + 3)), dY(app.parms.get(ii + 4)));
        }
      }
      double rot = app.parms.get(5 + (coords - 1) * 2);
      outline.closePath();
      AffineTransform at = new AffineTransform();
      at.translate(x1, y1);
      at.rotate(Math.toRadians(360 - rot));   // Spec says rotation is counterclockwise
      addToBoard(at.createTransformedShape(outline), isDark);
    } else {
      System.out.println("flashAperture() Aperture type = " + app.type + " not implemented, exposure is " + (isDark ? "DRK" : "CLR"));
      for (double val : app.parms) {
        System.out.print("  " + val);
      }
      System.out.println();
    }
    if (holeIndex > 0) {
      // Draw hole in Aperture
      double diam = dW(app.parms.get(holeIndex));
      addToBoard(new Ellipse2D.Double(x1 - diam / 2, y1 - diam / 2, diam, diam), false);
    }
  }

  /**
   * Draw a line that simulates drawing with a moving Aperture.
   * Note: the RS-274X spec says that "the solid circle and solid rectangle standard apertures are
   * the only apertures allowed for creating draw objects", so that's all this code implements.
   * @param x1 x coord of start point
   * @param y1 y coord of start point
   * @param x2 x coord of end point
   * @param y2 y coord of end point
   */
  private void interpolateAperture (Aperture app, double x1, double y1, double x2, double y2) {
    x1 = dX(x1);
    y1 = dY(y1);
    x2 = dX(x2);
    y2 = dY(y2);
    if (app.type == CIRCLE) {
      double diam = dW(app.parms.get(0));
      BasicStroke s1 = new BasicStroke((float) diam, BasicStroke.CAP_ROUND, BasicStroke.JOIN_ROUND);
      addToBoard(s1.createStrokedShape(new Line2D.Double(x1, y1, x2, y2)), isDark);
    } else if (app.type == RECTANGLE) {
      double wid = dW(app.parms.get(0));
      double hyt = dH(app.parms.get(1));
      double diam = Math.sqrt(wid * wid + hyt * hyt);
      BasicStroke s1 = new BasicStroke((float) diam, BasicStroke.CAP_BUTT, BasicStroke.JOIN_ROUND);
      addToBoard(s1.createStrokedShape(new Line2D.Double(x1, y1, x2, y2)), isDark);
      // Draw rectangle at start and end points to simulate Gerber's rectangular interpolation
      addToBoard(new Rectangle2D.Double(x1 - wid / 2, y1 - hyt / 2, wid, hyt), isDark);
      addToBoard(new Rectangle2D.Double(x2 - wid / 2, y2 - hyt / 2, wid, hyt), isDark);
    } else {
      System.out.println("interpolateAperture() Aperture type = " + app.type + " not implemented, exposure is " + (isDark ? "DRK" : "CLR"));
      for (double val : app.parms) {
        System.out.print("  " + val);
      }
      System.out.println();
    }
  }
}
