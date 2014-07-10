/**
 * This file is part of CamImportPlugins/SotonImportPlugins.
 * 
 * Copyright (C) 2011 intranda GmbH
 * 
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * @author Andrey Kozhushkov
 */
package de.intranda.goobi.plugins.utils;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.apache.commons.lang.StringUtils;
import org.apache.log4j.Logger;
import org.jdom.Attribute;
import org.jdom.Content;
import org.jdom.Document;
import org.jdom.Element;
import org.jdom.JDOMException;
import org.jdom.Namespace;
import org.jdom.input.SAXBuilder;
import org.jdom.output.XMLOutputter;
import org.jdom.xpath.XPath;

import ugh.dl.DocStruct;
import ugh.dl.Metadata;
import ugh.dl.MetadataType;
import ugh.dl.Person;
import ugh.dl.Prefs;
import ugh.dl.RomanNumeral;
import ugh.exceptions.DocStructHasNoTypeException;
import ugh.exceptions.MetadataTypeNotAllowedException;
import de.intranda.goobi.plugins.CSICMixedImport;
import de.schlichtherle.io.FileInputStream;
import de.sub.goobi.config.ConfigMain;

public class ModsUtils {

    /** Logger for this class. */
    private static final Logger logger = Logger.getLogger(ModsUtils.class);

    private static final Namespace NS_MODS = Namespace.getNamespace("mods", "http://www.loc.gov/mods/v3");
    private static final String TEMP_DIRECTORY = ConfigMain.getParameter("tempfolder");
    private static final String PREFIX_SERIES = "Núm. Serie, ";
    private static final String PREFIX_VOLUME = "Vol. ";

    private static HashMap<String, String> seriesInfo = new HashMap<String, String>(); // Name and identifier of related Item "series"
    private static String seriesInfoFilename = "seriesInfo.ser";
    private static String personRoleMapFilename = "person_role_map.xml";
    private static ArrayList<String> anchorMetadataList = new ArrayList<String>(Arrays.asList("Fonds", "FondsGroup"));
    private static ArrayList<String> volumeExclusiveMetadataList = new ArrayList<String>(Arrays.asList("Taxonomy"));
    private static ArrayList<String> taxonomyFieldsList = new ArrayList<String>(Arrays.asList("titleinfo", "topic", "genre", "geographic",
            "cartographics", "temporal", "name", "occupation"));
    private static DecimalFormat volumeNumberFormat = new DecimalFormat("00");
    private static HashMap<String, String> personRoleMap = new HashMap<String, String>();

    /**
     * Writes the given JDOM document into a file.
     * 
     * @param folderName Folder in which to write the destination file.
     * @param fileName Name of the destination file.
     * @param doc JDOM document containing the data.
     * @throws FileNotFoundException
     * @throws IOException
     */
    public static void writeXmlToFile(String folderName, String fileName, Document doc) {
        try {
            File folder = new File(folderName);
            if (!folder.exists()) {
                folder.mkdirs();
            }
            new XMLOutputter().output(doc, new FileOutputStream(folder.getAbsolutePath() + File.separator + fileName));
        } catch (FileNotFoundException e) {
            logger.error(e.getMessage());
        } catch (IOException e) {
            logger.error(e.getMessage());
        }
    }

    private static void writeFile(File file, Object obj) {
        try {
            FileOutputStream fs = new FileOutputStream(file);
            ObjectOutputStream os = new ObjectOutputStream(fs);
            os.writeObject(obj);
            os.close();
        } catch (IOException e) {
            logger.error("Error writing binary file", e);
        }
    }

    public static Document createEmptyGoobiDoc(Namespace mets, Namespace mods, Namespace goobi) {
        Document doc = new Document();

        doc.setRootElement(new Element("mets", mets));
        Element root = doc.getRootElement();
        Element dmdSec = new Element("dmdSec", mets);
        dmdSec.setAttribute("ID", "DMDLOG_0000");
        root.addContent(dmdSec);
        Element mdWrap = new Element("mdWrap", mets);
        mdWrap.setAttribute("MDTYPE", "MODS");
        dmdSec.addContent(mdWrap);
        Element xmlData = new Element("xmlData", mets);
        mdWrap.setContent(xmlData);
        Element modsEle = new Element("mods", mods);
        xmlData.setContent(modsEle);
        Element extension = new Element("extension", mods);
        modsEle.addContent(extension);
        Element goobiEle = new Element("goobi", goobi);
        extension.addContent(goobiEle);
        Element dmdSec2 = new Element("dmdSec", mets);
        dmdSec.setAttribute("ID", "DMDPHYS_0000");
        root.addContent(dmdSec2);
        Element mdWrap2 = new Element("mdWrap", mets);
        mdWrap.setAttribute("MDTYPE", "MODS");
        dmdSec2.addContent(mdWrap2);
        Element xmlData2 = new Element("xmlData", mets);
        mdWrap2.setContent(xmlData2);
        Element modsEle2 = new Element("mods", mods);
        xmlData2.setContent(modsEle2);
        Element extension2 = new Element("extension", mods);
        modsEle2.addContent(extension2);
        Element goobiEle2 = new Element("goobi", goobi);
        extension2.addContent(goobiEle2);

        return doc;

    }

    private static Object readFile(File file) {
        FileInputStream fis;
        Object obj = null;
        try {
            fis = new FileInputStream(file);
            ObjectInputStream ois = new ObjectInputStream(fis);
            obj = ois.readObject();
            ois.close();
        } catch (FileNotFoundException e) {
            logger.warn("No binary file exists to read. Aborting.");
        } catch (IOException e) {
            logger.error("Error reading binary file", e);
        } catch (ClassNotFoundException e) {
            logger.error("Error reading object from binary file", e);
        }
        return obj;
    }

    private static void fillPersonRoleMap() {
        personRoleMap = new HashMap<String, String>();

        personRoleMap.put("adaptor", "Adapter");
        personRoleMap.put("adapt", "Adapter");
        personRoleMap.put("adp", "Adapter");
        personRoleMap.put("adapter", "Adapter");

        personRoleMap.put("arreglista musical", "Arranger");
        personRoleMap.put("arr", "Arranger");
        personRoleMap.put("arreglista", "Arranger");
        personRoleMap.put("arranger", "Arranger");

        personRoleMap.put("autor", "Author");
        personRoleMap.put("aut", "Author");
        personRoleMap.put("author", "Author");

        personRoleMap.put("autor literario", "AuthorLit");
        personRoleMap.put("aut lit", "AuthorLit");

        personRoleMap.put("colaborador", "Collaborator");
        personRoleMap.put("col", "Collaborator");
        personRoleMap.put("collaborator", "Collaborator");

        personRoleMap.put("comentarista", "Commentator");
        personRoleMap.put("com", "Commentator");
        personRoleMap.put("commentator", "Commentator");
        personRoleMap.put("cmm", "Commentator");

        personRoleMap.put("compilador", "Compiler");
        personRoleMap.put("comp", "Compiler");
        personRoleMap.put("compiler", "Compiler");
        personRoleMap.put("com", "Compiler");

        personRoleMap.put("composer", "Composer");
        personRoleMap.put("cmp", "Composer");

        personRoleMap.put("continuador", "Continuator");
        personRoleMap.put("cont", "Continuator");

        personRoleMap.put("coordinador", "Coordinator");
        personRoleMap.put("coord", "Coordinator");
        personRoleMap.put("coordinator", "Coordinator");

        personRoleMap.put("copier", "Copier");
        personRoleMap.put("frg", "Copier");
        personRoleMap.put("copista", "Copier");
        personRoleMap.put("cop", "Copier");

        personRoleMap.put("corrector", "Corrector");
        personRoleMap.put("corr", "Corrector");
        personRoleMap.put("crr", "Corrector");

        personRoleMap.put("dibujante", "IllustratorArtist");
        personRoleMap.put("dib", "IllustratorArtist");
        personRoleMap.put("illustrador", "IllustratorArtist");
        personRoleMap.put("illu", "IllustratorArtist");

        personRoleMap.put("cwt", "Annotator");
        personRoleMap.put("anot", "Annotator");
        personRoleMap.put("ann", "Annotator");
        personRoleMap.put("annotator", "Annotator");

        personRoleMap.put("director", "Director");
        personRoleMap.put("dir", "Director");
        personRoleMap.put("drt", "Director");

        personRoleMap.put("editor", "Editor");
        personRoleMap.put("ed", "Editor");
        personRoleMap.put("edt", "Editor");

        personRoleMap.put("encuadernado", "Binder");
        personRoleMap.put("enc", "Binder");
        personRoleMap.put("encuadernación", "Binder");
        personRoleMap.put("encuadernador", "Binder");
        personRoleMap.put("binder", "Binder");
        personRoleMap.put("bnd", "Binder");

        personRoleMap.put("fotógrafo", "Photographer");
        personRoleMap.put("fot", "Photographer");
        personRoleMap.put("photographer", "Photographer");
        personRoleMap.put("pht", "Photographer");

        personRoleMap.put("impresor", "Printer");
        personRoleMap.put("imp", "Printer");
        personRoleMap.put("printer", "Printer");
        personRoleMap.put("prt", "Printer");

        personRoleMap.put("interprete", "Actor");
        personRoleMap.put("int", "Actor");
        personRoleMap.put("interpreter", "Actor");

        personRoleMap.put("prologuista", "IntroductionAuthor");
        personRoleMap.put("pr", "IntroductionAuthor");
        personRoleMap.put("author of introduction, etc", "IntroductionAuthor");
        personRoleMap.put("aui", "IntroductionAuthor");

        personRoleMap.put("recopilador", "Compiler");
        personRoleMap.put("rec", "Compiler");

        personRoleMap.put("collector", "Collector");
        personRoleMap.put("col", "Collector");

        personRoleMap.put("redactor", "Redactor");
        personRoleMap.put("red", "Redactor");
        personRoleMap.put("redactor", "Redactor");

        personRoleMap.put("refundidor", "Adapter");
        personRoleMap.put("ref", "Adapter");

        personRoleMap.put("revisor", "Revisor");
        personRoleMap.put("rev", "Revisor");

        personRoleMap.put("seleccionador", "Coordinator");
        personRoleMap.put("sel", "Coordinator");

        personRoleMap.put("teacher", "Teacher");
        personRoleMap.put("tch", "Teacher");

        personRoleMap.put("traductor", "Translator");
        personRoleMap.put("trad", "Translator");
        personRoleMap.put("translator", "Translator");
        personRoleMap.put("trl", "Translator");

        personRoleMap.put("transcriptor", "Transcriber");
        personRoleMap.put("transcrip", "Transcriber");
        personRoleMap.put("transcriber", "Transcriber");
        personRoleMap.put("trc", "Transcriber");

    }

    /**
     * 
     * @param pres
     * @param dsLogical
     * @param dsPhysical
     * @param eleMods
     * @param mappingFile
     * @throws IOException
     * @throws JDOMException
     */
    @SuppressWarnings("unchecked")
    public static void parseModsSection(CSICMixedImport plugin, DocStruct dsLogical, DocStruct dsAnchor, DocStruct dsPhysical, Element eleMods,
            int volumeNo, String pieceDesignation) throws JDOMException, IOException {
        fillPersonRoleMap();
        String mappingFileName = CSICMixedImport.MODS_MAPPING_FILE;
        Prefs prefs = plugin.getPrefs();
        String suffix = plugin.getCurrentSuffix();
        boolean writeAllMetadataToAnchor = false;
        if (dsAnchor != null && dsAnchor.getType().getName().contentEquals("MultiVolumeWork")) {
            writeAllMetadataToAnchor = true;
        }
        File mappingFile = new File(mappingFileName);

        File seriesInfoFile = new File(TEMP_DIRECTORY, seriesInfoFilename);
        if (seriesInfoFile.isFile()) {
            logger.debug("Reading data from " + seriesInfoFile.getName());
            Object obj = readFile(seriesInfoFile);
            if (obj instanceof HashMap<?, ?>) {
                seriesInfo = (HashMap<String, String>) obj;
            }
        }

        Document doc = new Document();
        Element eleNewMods = (Element) eleMods.clone();
        doc.setRootElement(eleNewMods);
        Document mapDoc = new SAXBuilder().build(mappingFile);
        String seriesTitle = null;
        String seriesID = null;
        List<String> publicationYears = new ArrayList<String>();
        for (Object obj : mapDoc.getRootElement().getChildren("metadata", null)) {
            Element eleMetadata = (Element) obj;
            String mdName = eleMetadata.getChildTextTrim("name", null);
            if ("location".equals(mdName)) {
                // write location info
                int counter = 0;
                List<Element> eleXpathList = eleMetadata.getChildren("xpath", null);
                if (eleXpathList == null || eleXpathList.isEmpty()) {
                    continue;
                }

                String query = eleXpathList.get(0).getTextTrim();
                XPath xpath;
                List<Element> eleValueList = queryNodes(doc, query);

                for (Element element : eleValueList) {

                    int locationVolumeNo = getVolumeNumberFromLocation(element);
                    if (locationVolumeNo > 0 && locationVolumeNo != volumeNo) {
                        continue;
                    }

                    String shelfmarkSource = null;
                    String physicalLocation = null;
                    String physicalCollection = null;
                    String localPieceDesignation = null;
                    int localVolumeNo = -1;
                    boolean isCurrentColume = true;

                    Element eleShelfmarkSource = element.getChild("shelfLocator", NS_MODS);
                    if (eleShelfmarkSource != null) {
                        shelfmarkSource = eleShelfmarkSource.getValue();
                    }
                    Element elePhysLocation = element.getChild("physicalLocation", NS_MODS);
                    if (elePhysLocation != null) {
                        physicalLocation = elePhysLocation.getValue();
                    }
                    Element eleHoldingSimple = element.getChild("holdingSimple", NS_MODS);
                    if (eleHoldingSimple != null) {
                        Element eleCopyInformation = eleHoldingSimple.getChild("copyInformation", NS_MODS);
                        if (eleCopyInformation != null) {
                            Element elePhysicalCollection = eleCopyInformation.getChild("subLocation", NS_MODS);
                            if (elePhysicalCollection != null) {
                                physicalCollection = elePhysicalCollection.getValue();
                            }
                            Element elePieceDesignation = eleCopyInformation.getChild("pieceDesignation", NS_MODS);
                            if (elePieceDesignation != null) {
                                localPieceDesignation = elePieceDesignation.getValue();
                            }
                            Element eleVolumeNo = eleCopyInformation.getChild("VolumeNo", NS_MODS);
                            if (eleVolumeNo == null) {
                                eleVolumeNo = eleCopyInformation.getChild("VolumeLabel", NS_MODS);
                            }
                            if (eleVolumeNo != null) {
                                String volumeString = eleVolumeNo.getValue().replaceAll("\\D", "");
                                if (volumeString != null && !volumeString.isEmpty()) {
                                    localVolumeNo = Integer.valueOf(volumeString);
                                }
                            }
                        }
                    }

                    if (localPieceDesignation == null) {
                        localPieceDesignation = pieceDesignation;
                    }

                    // if (pieceDesignation != null && localPieceDesignation.contentEquals(pieceDesignation)) {
                    // This is either the correct volume or no volume is specified.
                    try {
                        String mdPrefix = "";
                        if (counter > 0) {
                            mdPrefix = "copy" + volumeNumberFormat.format(counter);
                        }

                        if (shelfmarkSource != null) {
                            MetadataType shelfmarkSourceType = prefs.getMetadataTypeByName(mdPrefix + "shelfmarksource");
                            Metadata shelfmarkSourceMetadata = new Metadata(shelfmarkSourceType);
                            shelfmarkSourceMetadata.setValue(shelfmarkSource);
                            dsPhysical.addMetadata(shelfmarkSourceMetadata);
                        }
                        if (physicalLocation != null) {
                            MetadataType physicalLocationType = prefs.getMetadataTypeByName(mdPrefix + "physicalLocation");
                            Metadata physicalLocationMetadata = new Metadata(physicalLocationType);
                            physicalLocationMetadata.setValue(physicalLocation);
                            dsPhysical.addMetadata(physicalLocationMetadata);
                        }
                        if (physicalCollection != null) {
                            MetadataType physicalCollectionType = prefs.getMetadataTypeByName(mdPrefix + "physicalCollection");
                            Metadata physicalCollectionMetadata = new Metadata(physicalCollectionType);
                            physicalCollectionMetadata.setValue(physicalCollection);
                            dsPhysical.addMetadata(physicalCollectionMetadata);
                        }

                        if (localPieceDesignation != null) {
                            MetadataType pieceDesignationType = prefs.getMetadataTypeByName(mdPrefix + "pieceDesignation");
                            Metadata pieceDesignationMetadata = new Metadata(pieceDesignationType);
                            pieceDesignationMetadata.setValue(localPieceDesignation);
                            dsPhysical.addMetadata(pieceDesignationMetadata);
                        }

                        if (counter < 10) {
                            counter++;
                        }

                    } catch (MetadataTypeNotAllowedException e) {
                        logger.warn(e.getMessage());
                    }
                    // }
                }
                continue;
            }

            MetadataType mdType = prefs.getMetadataTypeByName(mdName);
            if (mdType != null) {
                List<Element> eleXpathList = eleMetadata.getChildren("xpath", null);
                if (mdType.getIsPerson()) {
                    // Persons
                    for (Element eleXpath : eleXpathList) {
                        String query = eleXpath.getTextTrim();
                        XPath xpath;
                        List<Element> eleValueList = queryNodes(doc, query);
                        if (eleValueList != null) {
                            for (Element eleValue : eleValueList) {
                                String name = "";
                                String firstName = "";
                                String lastName = "";
                                String termsOfAddress = "";
                                String roleTerm = "";
                                String typeName = "";

                                for (Object o : eleValue.getChildren()) {
                                    Element eleNamePart = (Element) o;
                                    if (eleNamePart.getName().contentEquals("role")) {
                                        Element eleRoleTerm = eleNamePart.getChild("roleTerm", null);
                                        if (eleRoleTerm != null) {
                                            roleTerm = eleRoleTerm.getValue();
                                        }
                                    } else {
                                        String type = eleNamePart.getAttributeValue("type");
                                        if (type == null || type.isEmpty()) {
                                            // no type
                                            name = eleNamePart.getValue();
                                        } else if (type.contentEquals("date")) {
                                            // do nothing?
                                        } else if (type.contentEquals("termsOfAddress")) {
                                            termsOfAddress = eleNamePart.getValue();
                                        } else if (type.contentEquals("given")) {
                                            firstName = eleNamePart.getValue();
                                        } else if (type.contentEquals("family")) {
                                            lastName = eleNamePart.getValue();
                                        }
                                    }
                                }

                                // set metadata type to role
                                if (roleTerm != null && !roleTerm.isEmpty()) {
                                    roleTerm = roleTerm.replaceAll("\\.", "");
                                    typeName = personRoleMap.get(roleTerm.toLowerCase());
                                    if (typeName == null) {
                                        String[] parts = roleTerm.split(" ");
                                        if (parts != null && parts.length > 0) {
                                            typeName = personRoleMap.get(parts[0].toLowerCase());
                                        }
                                        if (typeName == null) {
                                            typeName = mdName;
                                        }
                                    }
                                } else {
                                    // with no role specified, assume it is an author
                                    typeName = "Author";
                                }
                                mdType = prefs.getMetadataTypeByName(typeName);

                                if (name.contains(",")) {
                                    String[] nameSplit = name.split("[,]");
                                    if (nameSplit.length > 0 && StringUtils.isEmpty(lastName)) {
                                        lastName = nameSplit[0].trim();
                                    }
                                    if (nameSplit.length > 1 && StringUtils.isEmpty(firstName)) {
                                        for (int i = 1; i < nameSplit.length; i++) {
                                            firstName += nameSplit[i].trim() + ", ";
                                        }
                                        firstName = firstName.substring(0, firstName.length() - 2);
                                    }
                                } else {
                                    lastName = name;
                                }

                                if (StringUtils.isNotEmpty(lastName)) {
                                    try {
                                        Person person = new Person(mdType);
                                        person.setFirstname(firstName);
                                        person.setLastname(lastName);
                                        person.setRole(mdType.getName());
                                        if (eleMetadata.getAttribute("logical") != null
                                                && eleMetadata.getAttributeValue("logical").equalsIgnoreCase("true")) {

                                            dsLogical.addPerson(person);
                                            if (writeAllMetadataToAnchor) {
                                                dsAnchor.addPerson(person);
                                            }

                                        }
                                    } catch (MetadataTypeNotAllowedException e) {
                                        logger.warn(e.getMessage());
                                    }
                                }
                            }
                        }
                    }

                } else {
                    // Regular metadata
                    List<String> values = new ArrayList<String>();
                    String separator = " ";
                    if (eleMetadata.getAttribute("separator") != null) {
                        separator = eleMetadata.getAttributeValue("separator");
                    }
                    for (Element eleXpath : eleXpathList) {
                        String query = eleXpath.getTextTrim();
                        // logger.debug("XPath: " + query);
                        XPath xpath = XPath.newInstance(query);
                        xpath.addNamespace(NS_MODS);
                        List eleValueList = xpath.selectNodes(doc);
                        if (eleValueList != null) {
                            if (mdName.contentEquals("Taxonomy")) {
                                for (Object objValue : eleValueList) {
                                    if (objValue instanceof Element) {
                                        Element eleValue = (Element) objValue;
                                        List<Element> subjectChildren = eleValue.getChildren();
                                        String value = "";
                                        for (Element element : subjectChildren) {
                                            if (taxonomyFieldsList.contains(element.getName().toLowerCase())) {
                                                List<Element> subElements = element.getChildren();
                                                if (subElements != null && !subElements.isEmpty()) {
                                                    String subValue = "";
                                                    for (Element subElement : subElements) {
                                                        if (subElement.getValue() != null && !subElement.getValue().trim().isEmpty()) {
                                                            subValue = subValue + " " + subElement.getValue();
                                                        }
                                                    }
                                                    value = value + separator + subValue.trim();
                                                } else if (element.getValue() != null && !element.getValue().trim().isEmpty()) {
                                                    value = value + separator + element.getValue();
                                                }
                                            }
                                        }
                                        if (value.length() > separator.length()) {
                                            value = value.substring(separator.length()).trim();
                                            values.add(value);
                                        }
                                    }
                                }
                            } else {
                                int count = 0;
                                for (Object objValue : eleValueList) {
                                    String value = null;
                                    if (objValue instanceof Element) {
                                        Element eleValue = (Element) objValue;
                                        logger.debug("mdType: " + mdType.getName() + "; Value: " + eleValue.getTextTrim());
                                        value = getElementValue(eleValue, ", ");
                                        //										value = eleValue.getTextTrim();
                                    } else if (objValue instanceof Attribute) {
                                        Attribute atrValue = (Attribute) objValue;
                                        logger.debug("mdType: " + mdType.getName() + "; Value: " + atrValue.getValue());
                                        value = atrValue.getValue();
                                    }
                                    if (value != null && values.size() <= count) {
                                        values.add(value);
                                    } else if (value != null) {
                                        value = values.get(count) + separator + value;
                                        values.set(count, value);
                                    }
                                    count++;
                                }
                            }
                        }
                    }

                    for (String value : values) {

                        if (mdType.getName().contentEquals("CurrentNoSorting")) {
                            value = correctCurrentNoSorting(value);
                        } else if (mdType.getName().contentEquals("CurrentNo")) {
                            value = formatVolumeString(value, PREFIX_SERIES);
                        } else if (!writeAllMetadataToAnchor && mdType.getName().contentEquals("TitleDocParallel")) {
                            seriesTitle = value;
                        }

                        if (!writeAllMetadataToAnchor && anchorMetadataList.contains(mdType.getName()) && dsAnchor != null) {
                            // if (mdType.getName().contentEquals("singleDigCollection") && dsSeries != null) {
                            try {
                                if (value.length() > 0) {
                                    Metadata metadata = new Metadata(mdType);
                                    metadata.setValue(value);
                                    logger.debug("Found metadata: " + metadata.getType().getName());
                                    if (eleMetadata.getAttribute("logical") != null
                                            && eleMetadata.getAttributeValue("logical").equalsIgnoreCase("true")) {
                                        logger.debug("Added metadata \"" + metadata.getValue() + "\" to logical structure");
                                        dsAnchor.addMetadata(metadata);
                                    }
                                }
                            } catch (MetadataTypeNotAllowedException e) {
                                logger.warn(e.getMessage());
                            }
                        }
                        try {
                            if (value.length() > 0) {
                                Metadata metadata = new Metadata(mdType);
                                metadata.setValue(value);
                                // logger.debug("Found metadata: " + metadata.getType().getName());
                                if (eleMetadata.getAttribute("logical") != null && eleMetadata.getAttributeValue("logical").equalsIgnoreCase("true")) {
                                    // logger.debug("Added metadata \"" + metadata.getValue() + "\" to logical structure");

                                    if (mdName.contentEquals("PublicationStart") || mdName.contentEquals("PublicationEnd")) {
                                        publicationYears.add(value);
                                        continue;
                                    }

                                    if (mdName.contentEquals("TitleDocMain")) {
                                        if (suffix != null && !suffix.isEmpty() && (plugin.addVolumeNoToTitle || !writeAllMetadataToAnchor)) {
                                            if (plugin.useSquareBracketsForVolume) {
                                                metadata.setValue(value + " [" + suffix + "]");
                                            } else {
                                                metadata.setValue(value + " (" + formatVolumeString(suffix, PREFIX_VOLUME) + ")");
                                            }
                                        }
                                        try {
                                            dsLogical.addMetadata(metadata);
                                            seriesTitle = value;
                                        } catch (MetadataTypeNotAllowedException e) {
                                            logger.warn(e.getMessage());
                                        }
                                    } else if (mdName.contentEquals("CatalogIDDigital")) {
                                        if (suffix != null && !suffix.isEmpty()) {
                                            metadata.setValue(value + "_" + suffix);
                                            if (writeAllMetadataToAnchor) {
                                                seriesID = value;
                                            }
                                        }
                                        try {
                                            dsLogical.addMetadata(metadata);
                                        } catch (MetadataTypeNotAllowedException e) {
                                            logger.warn(e.getMessage());
                                        }
                                    } else {
                                        try {
                                            dsLogical.addMetadata(metadata);
                                        } catch (MetadataTypeNotAllowedException e) {
                                            logger.warn(e.getMessage());
                                        }
                                        try {
                                            //Don't write volume exclusive metadata to anchor
                                            if (writeAllMetadataToAnchor && !volumeExclusiveMetadataList.contains(metadata.getType().getName())) {
                                                dsAnchor.addMetadata(metadata);
                                            }
                                        } catch (MetadataTypeNotAllowedException e) {
                                            logger.warn(e.getMessage());
                                        }
                                    }

                                }
                                if (eleMetadata.getAttribute("physical") != null
                                        && eleMetadata.getAttributeValue("physical").equalsIgnoreCase("true")) {
                                    // logger.debug("Added metadata \"" + metadata.getValue() + "\" to physical structure");
                                    dsPhysical.addMetadata(metadata);
                                }
                            }
                        } catch (MetadataTypeNotAllowedException e) {
                            logger.warn(e.getMessage());
                        }
                    }
                }

            } else {
                logger.warn("Metadata '" + mdName + "' is not defined in the ruleset.");
            }
        }

        //construct PublicationYear from Start and Enddate if necessary
        List<? extends Metadata> mdPublicationList = dsLogical.getAllMetadataByType(prefs.getMetadataTypeByName("PublicationYear"));
        if ((mdPublicationList == null || mdPublicationList.isEmpty()) && !publicationYears.isEmpty()) {
            Collections.sort(publicationYears);
            String value = publicationYears.get(0);
            if (publicationYears.size() > 1) {
                value += ("-" + publicationYears.get(publicationYears.size() - 1));
            }
            if (value != null && !value.trim().isEmpty()) {
                try {
                    Metadata mdPublicationYear = new Metadata(prefs.getMetadataTypeByName("PublicationYear"));
                    mdPublicationYear.setValue(value);

                    try {
                        dsLogical.addMetadata(mdPublicationYear);
                    } catch (MetadataTypeNotAllowedException e) {
                        logger.error(e.getMessage());
                    } catch (DocStructHasNoTypeException e) {
                        logger.error(e.getMessage());
                    }

                    if (writeAllMetadataToAnchor) {
                        try {
                            dsAnchor.addMetadata(mdPublicationYear);
                        } catch (MetadataTypeNotAllowedException e) {
                            logger.warn(e.getMessage());
                        } catch (DocStructHasNoTypeException e) {
                            logger.warn(e.getMessage());
                        }
                    }

                } catch (MetadataTypeNotAllowedException e) {
                    logger.error(e.getMessage());
                }

            }
        }

        // Code to handle related works, e.g. series, but only if we are not working within a MultiVolume
        if (!writeAllMetadataToAnchor) {

            String titleDocMain = null;
            String titleDocPart = null;
            List<String> values = new ArrayList<String>();

            //Get main title
            //for archivos
            String query = "/mods:mods/mods:note[@type='fonds']";
            List<Element> eleValueList = queryNodes(doc, query);
            if (eleValueList != null && !eleValueList.isEmpty()) {
                titleDocMain = eleValueList.get(0).getValue();
            } else {
                //for libraries
                query = "/mods:mods/mods:relatedItem[@type='series']/mods:titleInfo[not(@type)]/mods:title";
                eleValueList = queryNodes(doc, query);
                if (eleValueList != null && !eleValueList.isEmpty()) {
                    titleDocMain = eleValueList.get(0).getValue();
                } else {
                    query = "/mods:mods/mods:relatedItem[@type='series']/mods:titleInfo[@type='uniform']/mods:title";
                    eleValueList = queryNodes(doc, query);
                    if (eleValueList != null && !eleValueList.isEmpty()) {
                        titleDocMain = eleValueList.get(0).getValue();
                    }
                }
            }
            //add all finds to valueList
            if (eleValueList != null) {
                for (Element eleValue : eleValueList) {
                    if (eleValue.getText() != null && !eleValue.getText().isEmpty()) {
                        values.add(eleValue.getTextTrim());
                    }
                }
            }

            //Get part title
            //for archivos
            query = "/mods:mods/mods:note[@type='fondsGroup']";
            eleValueList = queryNodes(doc, query);
            if (eleValueList != null && !eleValueList.isEmpty()) {
                titleDocPart = eleValueList.get(0).getValue();
            } else {
                //for libraries
                query = "/mods:mods/mods:relatedItem[@type='series']/mods:titleInfo[not(@type)]/mods:partName";
                eleValueList = queryNodes(doc, query);
                if (eleValueList != null && !eleValueList.isEmpty()) {
                    titleDocPart = eleValueList.get(0).getValue();
                } else {
                    query = "/mods:mods/mods:relatedItem[@type='series']/mods:titleInfo[@type='uniform']/mods:partName";
                    eleValueList = queryNodes(doc, query);
                    if (eleValueList != null && !eleValueList.isEmpty()) {
                        titleDocPart = eleValueList.get(0).getValue();
                    }
                }
            }
            //add all finds to valueList
            if (eleValueList != null && !eleValueList.isEmpty()) {
                //if the main title is already in the list, add a separator char
                if (!values.isEmpty()) {
                    values.add("/");
                }
                for (Element eleValue : eleValueList) {
                    if (eleValue.getText() != null && !eleValue.getText().isEmpty()) {
                        values.add(eleValue.getTextTrim());
                        values.add("/");
                    }
                }
                if (values.get(values.size() - 1).equals("/")) {
                    values.remove(values.size() - 1);
                }
            }

            logger.debug("anchor title = " + titleDocMain);
            logger.debug("anchor part name = " + titleDocPart);

            //            if (dsAnchor != null && titleDocMain != null) {
            //                try {
            //                    Metadata mdTitleDocMain = new Metadata(prefs.getMetadataTypeByName("TitleDocMain"));
            //                    mdTitleDocMain.setValue(titleDocMain);
            //                    dsAnchor.addMetadata(mdTitleDocMain);
            //                } catch (MetadataTypeNotAllowedException e) {
            //                    logger.warn(e.getMessage());
            //                } catch (DocStructHasNoTypeException e) {
            //                    logger.warn(e.getMessage());
            //                }
            //            }
            //            if (dsAnchor != null && titleDocPart != null) {
            //                try {
            //                    Metadata mdTitleDocPart = new Metadata(prefs.getMetadataTypeByName("TitleDocPart"));
            //                    mdTitleDocPart.setValue(titleDocPart);
            //                    dsAnchor.addMetadata(mdTitleDocPart);
            //                } catch (MetadataTypeNotAllowedException e) {
            //                    logger.warn(e.getMessage());
            //                } catch (DocStructHasNoTypeException e) {
            //                    logger.warn(e.getMessage());
            //                }
            //            }

            if (values != null && !values.isEmpty()) {
                String value = "";
                for (String s : values) {
                    if (StringUtils.isNotEmpty(s)) {
                        value += " " + s;
                    }
                }
                value = value.trim();
                String[] valueParts = value.split("\\s");
                seriesTitle = "";
                HashMap<String, Boolean> valueMap = new HashMap<String, Boolean>();
                for (int i = 0; i < valueParts.length; i++) {
                    if (!valueMap.containsKey(valueParts[i])) {
                        seriesTitle += " " + valueParts[i];
                        valueMap.put(valueParts[i], true);
                    }
                }
                seriesTitle = seriesTitle.trim();
                logger.debug("related Series = " + seriesTitle);

                //write series title as
                if (dsAnchor != null && !seriesTitle.isEmpty()) {
                    try {
                        Metadata mdTitle = new Metadata(prefs.getMetadataTypeByName("TitleDocMain"));
                        mdTitle.setValue(value);
                        dsAnchor.addMetadata(mdTitle);
                    } catch (MetadataTypeNotAllowedException e) {
                        logger.warn(e.getMessage());
                    } catch (DocStructHasNoTypeException e) {
                        logger.warn(e.getMessage());
                    }
                }
            }
        }

        if (dsAnchor != null) {
            if (seriesID == null) {
                if (seriesTitle != null) {
                    seriesID = seriesInfo.get(seriesTitle);
                }
                if (seriesID == null) {
                    seriesID = "CSIC" + System.currentTimeMillis();
                    logger.debug("Series not found. creating new one: " + seriesID);
                }
            }
            if (seriesTitle == null) {
                seriesTitle = seriesID;
            }

            // Creating metadata for series
            try {
                MetadataType titleType = prefs.getMetadataTypeByName("TitleDocMain");
                MetadataType idType = prefs.getMetadataTypeByName("CatalogIDDigital");
                Metadata mdTitle;
                mdTitle = new Metadata(titleType);
                Metadata mdID = new Metadata(idType);
                mdTitle.setValue(seriesTitle);
                mdID.setValue(seriesID);

                dsAnchor.addMetadata(mdID);
                dsAnchor.addMetadata(mdTitle);

            } catch (MetadataTypeNotAllowedException e) {
                logger.warn(e.getMessage());
            }
        }

        // Create CurrentNo and CurrentNoSorting if necessary
        if (dsAnchor != null && suffix != null && !suffix.isEmpty()) {

            List<? extends Metadata> mdCurrentNoList = dsLogical.getAllMetadataByType(prefs.getMetadataTypeByName("CurrentNo"));
            if (!writeAllMetadataToAnchor || plugin.writeCurrentNoToMultiVolume) {
                if ((mdCurrentNoList == null || mdCurrentNoList.isEmpty())) {
                    // No current Number, so we create one
                    try {
                        String value = null;
                        Metadata md = new Metadata(prefs.getMetadataTypeByName("CurrentNo"));
                        if (writeAllMetadataToAnchor) {
                            value = formatVolumeString(suffix, PREFIX_VOLUME);
                        } else {
                            value = formatVolumeString(suffix, PREFIX_SERIES);
                        }
                        md.setValue(value);
                        dsLogical.addMetadata(md);
                    } catch (MetadataTypeNotAllowedException e) {
                        logger.warn(e.toString());
                    }
                }
            }

            List<? extends Metadata> mdCurrentNoSortList = dsLogical.getAllMetadataByType(prefs.getMetadataTypeByName("CurrentNoSorting"));
            if (!writeAllMetadataToAnchor || plugin.writeCurrentNoSortingToMultiVolume) {
                if (mdCurrentNoSortList == null || mdCurrentNoSortList.isEmpty() && !writeAllMetadataToAnchor) {
                    // No current Number, so we create one
                    try {
                        Metadata md = new Metadata(prefs.getMetadataTypeByName("CurrentNoSorting"));
                        String str = suffix;
                        if (str.contains("_")) {
                            str = suffix.split("_")[0];
                        }
                        if (str.startsWith("V")) {
                            str = str.substring(1);
                        }
                        str = correctCurrentNoSorting(str);
                        md.setValue(str);
                        dsLogical.addMetadata(md);
                    } catch (MetadataTypeNotAllowedException e) {
                        logger.warn(e.toString());
                    }
                }
            }
        }

        // write seriesInfo to file
        if (seriesTitle != null && !seriesTitle.isEmpty()) {
            seriesInfo.put(seriesTitle, seriesID);
            if (seriesInfoFile.isFile()) {
                logger.debug("deleting old seriesInfoFile");
                seriesInfoFile.delete();
            }
            writeFile(seriesInfoFile, seriesInfo);
        }
    }

    private static List<Element> queryNodes(Document doc, String query) throws JDOMException {
        XPath xpath = XPath.newInstance(query);
        xpath.addNamespace(NS_MODS);
        List<Element> eleValueList = xpath.selectNodes(doc);
        return eleValueList;
    }

    private static int getVolumeNumberFromLocation(Element element) {
        Iterator contentIterator = element.getDescendants();
        while (contentIterator.hasNext()) {
            Content content = (Content) contentIterator.next();
            if (content instanceof Element) {
                if (((Element) content).getName().toLowerCase().contains("volume")) {
                    Integer no = getNumberFromString(content.getValue());
                    if (no != null) {
                        return no;
                    }
                }
            }
        }
        return 0;
    }

    public static Integer getNumberFromString(String str) {
        if (str == null || str.trim().isEmpty()) {
            return null;
        }
        Integer ret = null;
        String onlyDecimal = str.replaceAll("\\D", "");
        if (onlyDecimal != null && !onlyDecimal.isEmpty()) {
            try {
                ret = Integer.valueOf(onlyDecimal);
                return ret;
            } catch (NumberFormatException e) {
                logger.trace("Failed to find digits in String. Trying to find a roman numeral");
            }
        }
        String[] parts = str.split("[\\W_]");
        if (parts != null) {
            for (String string : parts) {
                try {
                    RomanNumeral num = new RomanNumeral(string);
                    return num.intValue();
                } catch (NumberFormatException e) {
                    logger.trace(string + " is not a roman numeral");
                }
            }
        }
        return null;
    }

    private static String getElementValue(Element eleValue, String separator) {
        if (separator == null) {
            separator = " ";
        }
        String value = eleValue.getTextTrim() == null ? "" : eleValue.getTextTrim();
        List<Element> namePartList = eleValue.getChildren("namePart", null);
        if (namePartList != null && !namePartList.isEmpty()) {
            for (Element element : namePartList) {
                String namePart = element.getTextTrim();
                if (namePart != null && !namePart.isEmpty()) {
                    value += separator + namePart;
                }
            }
            if (value.startsWith(separator)) {
                value = value.substring(separator.length());
            }
        }
        return value;
    }

    private static String formatVolumeString(String value, String prefix) {
        int startIndex = 0;
        if (value.startsWith("V") || value.startsWith("0")) {
            startIndex = 1;
        } else if (value.startsWith("V0")) {
            startIndex = 2;
        }

        value = value.substring(startIndex);

        return prefix + value;
    }

    /**
     * 
     * @param dsLogical
     * @param dsPhysical
     * @param eleMods
     * @throws MetadataTypeNotAllowedException
     */
    @Deprecated
    public static void parseModsSectionOld(Prefs prefs, DocStruct dsLogical, DocStruct dsPhysical, Element eleMods) {
        for (Object objMeta : eleMods.getChildren()) {
            try {
                Element eleMeta = (Element) objMeta;
                // logger.debug("md: " + eleMeta.getName());
                if (eleMeta.getName().equals("titleInfo")) {
                    String localTitle = "";
                    if (eleMeta.getChild("nonSort", null) != null) {
                        localTitle += eleMeta.getChild("nonSort", null).getText();
                    }
                    if (eleMeta.getChild("title", null) != null) {
                        localTitle += eleMeta.getChild("title", null).getText();
                    }
                    logger.debug("LocalTitle = " + localTitle);
                    if (eleMeta.getAttribute("type") != null) {
                        if (eleMeta.getAttributeValue("type").equals("alternative")) {
                            Metadata mdTitle = new Metadata(prefs.getMetadataTypeByName("TitleDocParallel"));
                            dsLogical.addMetadata(mdTitle);
                            mdTitle.setValue(localTitle);
                        }
                    } else {
                        // Main title
                        // currentTitle = localTitle;
                        Metadata mdTitle = new Metadata(prefs.getMetadataTypeByName("TitleDocMain"));
                        dsLogical.addMetadata(mdTitle);
                        mdTitle.setValue(localTitle);
                        if (eleMeta.getChild("subTitle", null) != null) {
                            // Main subtitle
                            Metadata mdSubTitle = new Metadata(prefs.getMetadataTypeByName("TitleDocSub1"));
                            dsLogical.addMetadata(mdSubTitle);
                            mdSubTitle.setValue(eleMeta.getChild("subTitle", null).getTextTrim());
                        }
                    }

                } else if (eleMeta.getName().equals("name")) {
                    if (eleMeta.getAttributeValue("type").equals("personal")) {
                        String name = "";
                        String lastName = "";
                        String firstName = "";
                        for (Object obj : eleMeta.getChildren("namePart", null)) {
                            Element eleNamePart = (Element) obj;
                            if (eleNamePart.getAttribute("type") != null) {
                                if (eleNamePart.getAttributeValue("type").equals("family")) {
                                    lastName = eleMeta.getChild("namePart", null).getAttributeValue("type");
                                } else if (eleNamePart.getAttributeValue("type").equals("given")) {
                                    firstName = eleMeta.getChild("namePart", null).getAttributeValue("type");
                                } else if (eleNamePart.getAttributeValue("type").equals("date")) {
                                    // TODO currently not supported by the ruleset
                                }
                            } else {
                                name += eleMeta.getChild("namePart", null).getText();
                            }
                        }
                        if (name.contains(",")) {
                            String[] nameSplit = name.split("[,]");
                            if (nameSplit.length > 0 && StringUtils.isEmpty(lastName)) {
                                lastName = nameSplit[0].trim();
                            }
                            if (nameSplit.length > 1 && StringUtils.isEmpty(firstName)) {
                                firstName = nameSplit[1].trim();
                            }
                        } else {
                            lastName = name;
                        }

                        Person person = new Person(prefs.getMetadataTypeByName("Author"));
                        dsLogical.addPerson(person);
                        person.setFirstname(firstName);
                        person.setLastname(lastName);
                        person.setRole("Author");
                    } else if (eleMeta.getAttributeValue("type").equals("corporate")) {
                        // TODO currently not supported by the ruleset
                    }
                } else if (eleMeta.getName().equals("originInfo")) {
                    for (Object obj : eleMeta.getChildren()) {
                        Element ele = (Element) obj;
                        if (ele.getName().equals("place")) {
                            Element elePlaceTerm = ele.getChild("placeTerm", null);
                            if (elePlaceTerm != null && elePlaceTerm.getAttribute("type") != null) {
                                if (elePlaceTerm.getAttributeValue("type").equals("text")) {
                                    Metadata metadata = new Metadata(prefs.getMetadataTypeByName("PlaceOfPublication"));
                                    dsLogical.addMetadata(metadata);
                                    metadata.setValue(elePlaceTerm.getTextTrim());
                                } else if (elePlaceTerm.getAttributeValue("type").equals("code")) {
                                    // TODO currently not supported by the ruleset
                                }
                            }
                        } else if (ele.getName().equals("publisher")) {
                            Metadata metadata = new Metadata(prefs.getMetadataTypeByName("PublisherName"));
                            dsLogical.addMetadata(metadata);
                            metadata.setValue(ele.getTextTrim());
                        } else if (ele.getName().equals("dateIssued")) {
                            if (ele.getAttribute("point") != null) {
                                if (ele.getAttributeValue("point").equals("start")) {
                                    Metadata metadata = new Metadata(prefs.getMetadataTypeByName("PublicationStart"));
                                    dsLogical.addMetadata(metadata);
                                    metadata.setValue(ele.getTextTrim());
                                } else if (ele.getAttributeValue("point").equals("end")) {
                                    Metadata metadata = new Metadata(prefs.getMetadataTypeByName("PublicationEnd"));
                                    dsLogical.addMetadata(metadata);
                                    metadata.setValue(ele.getTextTrim());
                                }
                            } else {
                                Metadata metadata = new Metadata(prefs.getMetadataTypeByName("PublicationYear"));
                                dsLogical.addMetadata(metadata);
                                metadata.setValue(ele.getTextTrim());
                            }
                        } else if (ele.getName().equals("dateCreated")) {
                            Metadata metadata = new Metadata(prefs.getMetadataTypeByName("PublicationYear"));
                            dsLogical.addMetadata(metadata);
                            metadata.setValue(ele.getTextTrim());
                        }
                    }
                } else if (eleMeta.getName().equals("language")) {
                    Element eleLanguageTerm = eleMeta.getChild("languageTerm", null);
                    if (eleLanguageTerm != null && eleLanguageTerm.getAttribute("authority") != null
                            && eleLanguageTerm.getAttributeValue("authority").equals("iso639-2b")) {
                        String language = eleMeta.getChildTextTrim("languageTerm", null);
                        Metadata metadata = new Metadata(prefs.getMetadataTypeByName("DocLanguage"));
                        dsLogical.addMetadata(metadata);
                        metadata.setValue(language);
                    }
                } else if (eleMeta.getName().equals("physicalDescription")) {
                    for (Object obj : eleMeta.getChildren()) {
                        Element ele = (Element) obj;
                        if (ele.getName().equals("extent")) {
                            Metadata metadata = new Metadata(prefs.getMetadataTypeByName("SizeSourcePrint"));
                            dsLogical.addMetadata(metadata);
                            metadata.setValue(ele.getTextTrim());
                        }
                    }
                } else if (eleMeta.getName().equals("recordInfo")) {
                    for (Object obj : eleMeta.getChildren()) {
                        Element ele = (Element) obj;
                        if (ele.getName().equals("recordIdentifier")) {
                            Metadata metadata = new Metadata(prefs.getMetadataTypeByName("CatalogIDDigital"));
                            dsLogical.addMetadata(metadata);
                            metadata.setValue(ele.getTextTrim());
                            // currentIdentifier = metadata.getValue();
                        }
                    }
                } else if (eleMeta.getName().equals("location")) {
                    for (Object obj : eleMeta.getChildren()) {
                        Element ele = (Element) obj;
                        if (ele.getName().equals("physicalLocation")) {
                            Metadata metadata = new Metadata(prefs.getMetadataTypeByName("physicallocation"));
                            dsLogical.addMetadata(metadata);
                            dsPhysical.addMetadata(metadata);
                            metadata.setValue(ele.getTextTrim());
                        } else if (ele.getName().equals("shelfLocation")) {
                            Metadata metadata = new Metadata(prefs.getMetadataTypeByName("shelfmarksource"));
                            dsLogical.addMetadata(metadata);
                            dsPhysical.addMetadata(metadata);
                            metadata.setValue(ele.getTextTrim());
                        }
                    }
                }
            } catch (MetadataTypeNotAllowedException e) {
                logger.warn(e.getMessage());
            }
        }
    }

    /**
     * Returns the document's identifier, or a timestamp if the record has none
     * 
     * @param prefs
     * @param ds
     * @return
     * @throws MetadataTypeNotAllowedException
     * @throws DocStructHasNoTypeException
     */
    public static String getIdentifier(Prefs prefs, DocStruct ds) throws MetadataTypeNotAllowedException, DocStructHasNoTypeException {
        String ret = null;

        MetadataType mdTypeId = prefs.getMetadataTypeByName("CatalogIDDigital");
        if (ds.getAllMetadataByType(mdTypeId) != null && !ds.getAllMetadataByType(mdTypeId).isEmpty()) {
            Metadata mdId = ds.getAllMetadataByType(mdTypeId).get(0);
            ret = mdId.getValue();
        } else {
            Metadata mdId = new Metadata(mdTypeId);
            ds.addMetadata(mdId);
            mdId.setValue(String.valueOf(System.currentTimeMillis()));
            ret = mdId.getValue();
        }

        return ret;
    }

    /**
     * Returns the document's title.
     * 
     * @param prefs
     * @param ds
     * @return
     * @throws MetadataTypeNotAllowedException
     * @throws DocStructHasNoTypeException
     */
    public static String getTitle(Prefs prefs, DocStruct ds) throws MetadataTypeNotAllowedException, DocStructHasNoTypeException {
        String ret = null;

        MetadataType mdTypeTitle = prefs.getMetadataTypeByName("TitleDocMain");
        if (ds.getAllMetadataByType(mdTypeTitle) != null && !ds.getAllMetadataByType(mdTypeTitle).isEmpty()) {
            Metadata mdTitle = ds.getAllMetadataByType(mdTypeTitle).get(0);
            ret = mdTitle.getValue();
        }

        return ret;
    }

    /**
     * Returns the document's author.
     * 
     * @param prefs
     * @param ds
     * @return
     * @throws MetadataTypeNotAllowedException
     * @throws DocStructHasNoTypeException
     */
    public static String getAuthor(Prefs prefs, DocStruct ds) throws MetadataTypeNotAllowedException, DocStructHasNoTypeException {
        String ret = null;

        MetadataType mdTypePerson = prefs.getMetadataTypeByName("Author");
        if (ds.getAllPersonsByType(mdTypePerson) != null && !ds.getAllPersonsByType(mdTypePerson).isEmpty()) {
            Person personAuthor = ds.getAllPersonsByType(mdTypePerson).get(0);
            ret = personAuthor.getLastname();
            if (StringUtils.isNotEmpty(personAuthor.getFirstname())) {
                ret += ", " + personAuthor.getFirstname();
            }
        }

        return ret;
    }

    public static String correctCurrentNoSorting(String inString) {

        String[] wsSplit = inString.split("\\s+");
        if (wsSplit.length == 0) {
            return "";
        } else if (wsSplit.length > 1) {
            for (String string : wsSplit) {
                String result = correctCurrentNoSorting(string);
                if (!result.isEmpty()) {
                    return result;
                }
            }
        }

        Pattern p = Pattern.compile("(\\D+)|(\\d+)");
        Matcher m = p.matcher(inString);
        String outString = "";
        while (m.find() && outString.isEmpty()) {
            String s = m.group();
            try {
                // Try to read a number
                int n = Integer.valueOf(s);
                outString = "" + n;
            } catch (NumberFormatException e) {
                logger.trace("No arabic numeral");
                try {
                    // Try to read a roman numeral
                    RomanNumeral rn = new RomanNumeral(s);
                    outString = "" + rn.intValue();
                } catch (NumberFormatException e1) {
                    logger.trace("No roman numeral");
                    outString = "";
                }
            }
        }
        return outString;
    }
}
